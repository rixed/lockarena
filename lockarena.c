#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>
#include <assert.h>
#include <limits.h>
#include <unistd.h>
#include <sys/time.h>
#include <pthread.h>
#include <signal.h>
#include <time.h>

#define NB_ELEMS(x) (sizeof(x) / sizeof(*(x)))

static unsigned method = 1, nb_threads = 100, nb_locks = 100;
static unsigned nb_claimed = 3, max_sleep_usec = 1000, duration = 1;
static unsigned long long timeout_nsec = 1000000ULL;
static pthread_t *pthread_ids;
static pthread_mutex_t *locks;
static uint64_t nb_errs, nb_trys;

/*
 * Just take it method : will quickly leads to deadlock
 */

static int just_lock(unsigned t, unsigned l)
{
	(void)t;
	return pthread_mutex_lock(locks+l);
}

static void just_unlock(unsigned t, unsigned l)
{
	(void)t;
	(void)pthread_mutex_unlock(locks+l);
}

/*
 * Dependency tracking (simple method)
 * Requires an additional global lock, but prevents deadlocks instead of detecting them afterward.
 * In number of threads or number of locks is really high a sparse representation would be required.
 */

static pthread_mutex_t m_lock = PTHREAD_MUTEX_INITIALIZER;
#define NB_BITS_PER_CELL 64
static uint64_t *thread_wq;	// list of locks we wait or hold, protected by m_lock.
static unsigned thread_stride;	// stride from one row to the next in the lock matrix
#define THREAD_HOLD(t, l)  (thread_wq[((t) << thread_stride) + (l)/NB_BITS_PER_CELL] & (1ULL << ((l)%NB_BITS_PER_CELL)))
#define THREAD_HOLD_GROUP(t, l)  (thread_wq[((t) << thread_stride) + (l)/NB_BITS_PER_CELL])
#define THREAD_SET(t, l)   (thread_wq[((t) << thread_stride) + (l)/NB_BITS_PER_CELL] |= (1ULL << ((l)%NB_BITS_PER_CELL)))
#define THREAD_CLEAR(t, l) (thread_wq[((t) << thread_stride) + (l)/NB_BITS_PER_CELL] &= ~(1ULL << ((l)%NB_BITS_PER_CELL)))

// This method allow us to detect recursive locks easily
static unsigned *recurs_count; 	// how many times each mutex is locked (protected by the lock itself, ensure you have it first!)

static unsigned upper_multiple_of(unsigned n, unsigned m)
{
	unsigned u = m;
	unsigned l = 1;
	while (u < n) {
		u += m;
		l ++;
	}
	return l;
}

// starting from (t, l) can we go back to target thread?
// As we are supposed to be cycle free we do not have to tag the matrix along the way.
static bool is_looping(unsigned t, unsigned l, unsigned target)
{
	for (unsigned ll = 0; ll < nb_locks; ll ++) {
		if (0 == (ll&(NB_BITS_PER_CELL-1))) {
			if (! THREAD_HOLD_GROUP(t, ll)) {
				ll += NB_BITS_PER_CELL-1;
				continue;
			}
		}
		if (! THREAD_HOLD(t, ll)) continue;
		if (ll == l) continue;	// we are not allowed to proceed to where we come from
		for (unsigned tt = 0; tt < nb_threads; tt ++) {
			if (! THREAD_HOLD(tt, ll)) continue;
			if (tt == t) continue;
			if (tt == target) return true;
			if (is_looping(tt, ll, target)) return true;
		}
	}

	return false;
}

static int matrix_lock(unsigned t, unsigned l)
{
	if (recurs_count[t * nb_locks + l] > 0) {
		recurs_count[t * nb_locks + l]++;
#		ifndef NDEBUG
		printf("thread %u: already got lock %u\n", t, l);
#		endif
		return 0;
	}

	if (0 != pthread_mutex_lock(&m_lock)) {
		assert(!"Cannot lock m_lock!?");
	}

	assert(! THREAD_HOLD(t, l));

	for (unsigned tt = 0; tt < nb_threads; tt ++) {
		if (! THREAD_HOLD(tt, l)) continue;
		if (is_looping(tt, l, t)) {
#			ifndef NDEBUG
			printf("thread %u: lock %u would deadlock\n", t, l);
#			endif
			pthread_mutex_unlock(&m_lock);

			return -1;
		}
	}

#	ifndef NDEBUG
	printf("thread %u: can safely wait for lock %u\n", t, l);
#	endif
	THREAD_SET(t, l);
	pthread_mutex_unlock(&m_lock);	// since I've said that I'm waiting for the lock I can safely release m_lock

	recurs_count[t * nb_locks + l]++;
	if (0 != pthread_mutex_lock(locks+l)) {
		assert(!"Cannot take lock?!");
	}
	return 0;
}

static void matrix_unlock(unsigned t, unsigned l)
{
	if (--recurs_count[t * nb_locks + l] > 0) {
		return;
	}

	if (0 != pthread_mutex_lock(&m_lock)) {
		assert(!"Cannot lock m_lock!?");
	}

	THREAD_CLEAR(t, l);

	pthread_mutex_unlock(&m_lock);

	(void)pthread_mutex_unlock(locks+l);
}

/*
 * Detect (using pthread_timed_lock) rather than prevent
 */

static int timed_lock(unsigned t, unsigned l)
{
	(void)t;

	struct timeval now;
    gettimeofday(&now, NULL);
	struct timespec timeout = {
		.tv_sec = now.tv_sec,
		.tv_nsec = now.tv_usec*1000ULL + timeout_nsec
	};
	return pthread_mutex_timedlock(locks+l, &timeout);
}

/*
 * Tests...
 */

static struct {
	char const *name;
	int (*lock)(unsigned, unsigned);
	void (*unlock)(unsigned, unsigned);
} methods[] = {
	{ "Just take it", just_lock, just_unlock },
	{ "Matrix", matrix_lock, matrix_unlock },
	{ "TimedLock", timed_lock, just_unlock },
};

static sig_atomic_t quit = 0;

static void *thread_run(void *idx)
{
	unsigned const t = (unsigned)(intptr_t)idx;

#	ifndef NDEBUG
	printf("thread %u: starting...\n", t);
#	endif

	while (! quit) {
		unsigned nb_res = rand() % nb_claimed;	// how many locks I'm going to claim
		unsigned claimed[nb_res];
		unsigned l, c = 0;
		__sync_add_and_fetch(&nb_trys, 1);
		for (l = 0; l < nb_res; l++) {
			unsigned const lock = rand() % nb_locks;
#			ifndef NDEBUG
			printf("thread %u: taking lock %u\n", t, lock);
#			endif
			if (0 == methods[method].lock(t, lock)) {
				claimed[c++] = lock;
			} else {
#				ifndef NDEBUG
				printf("thread %u: failed to lock %u\n", t, lock);
#				endif
				__sync_add_and_fetch(&nb_errs, 1);
				break;
			}
#			ifndef NDEBUG
			printf("thread %u: took lock %u\n", t, lock);
#			endif
		}
		if (l == nb_res) {	// do some work with the locks
			// Sleep for some time with my locks
			usleep(rand() % max_sleep_usec);
		}
		// Release all that was locked
		while (c --) {
#			ifndef NDEBUG
			printf("thread %u: releasing lock %u\n", t, claimed[c]);
#			endif
			methods[method].unlock(t, claimed[c]);
#			ifndef NDEBUG
			printf("thread %u: released lock %u\n", t, claimed[c]);
#			endif
		}
	}

	return NULL;
}

static void syntax(void)
{
	printf(
		"lockArena\nusage:\n"
		" -h            help (this)\n"
		" -m method     0 for no detection, 1 for dependency tracking, 2 for timedlocks\n"
		" -t nb_threads\n"
		" -l nb_locks\n"
		" -c nb_claim   number of required locks before each job\n"
		" -s usec       job duration (in microseconds)\n"
		" -d duration   number of seconds before the program (try to) terminate\n"
		" -T timeout    for timedlocks (in nanoseconds)\n");
}

int main(int nb_args, char **args)
{
	int opt;
	while ((opt = getopt(nb_args, args, "hm:t:l:c:s:d:T:")) != -1) {
		switch (opt) {
			case 'h':
				syntax();
				return EXIT_SUCCESS;
			case 'm':
				method = strtoul(optarg, NULL, 0);
				assert(method <= NB_ELEMS(methods));
				break;
			case 't':
				nb_threads = strtoul(optarg, NULL, 0);
				break;
			case 'l':
				nb_locks = strtoul(optarg, NULL, 0);
				break;
			case 'c':
				nb_claimed = strtoul(optarg, NULL, 0);
				break;
			case 's':
				max_sleep_usec = strtoul(optarg, NULL, 0);
				break;
			case 'd':
				duration = strtoul(optarg, NULL, 0);
				break;
			case 'T':
				timeout_nsec = strtoull(optarg, NULL, 0);
				break;
			case '?':
				syntax();
				return EXIT_FAILURE;
			case -1:
				break;
		}
	}

	printf(
		"Running %u threads, taking %u locks (amongst %u) before sleeping %uusecs, "
		"using method %s, repeating for %usecs...\n",
		nb_threads, nb_claimed, nb_locks, max_sleep_usec, methods[method].name, duration);

	srand(time(NULL));

	thread_stride = upper_multiple_of(nb_locks, NB_BITS_PER_CELL);
	pthread_ids = malloc(nb_threads * sizeof(*pthread_ids));
	locks = malloc(nb_locks * sizeof(*locks));
	recurs_count = calloc(nb_threads * nb_locks, sizeof(*recurs_count));
	size_t const thread_wq_sz = (nb_threads << thread_stride) * sizeof(*thread_wq);
	thread_wq = calloc(thread_wq_sz, 1);
	if (!pthread_ids || !locks || !thread_wq) {
		fprintf(stderr, "Cannot alloc.\n");
		return EXIT_FAILURE;
	}

	for (unsigned m = 0; m < nb_locks; m++) {
		pthread_mutex_init(locks+m, NULL);
	}

	for (unsigned t = 0; t < nb_threads; t++) {
		pthread_create(pthread_ids+t, NULL, thread_run, (void *)(intptr_t)t);
	}

	sleep(duration);
	printf("%"PRIu64" jobs done, %"PRIu64" errors (%.2f%%)\n", nb_trys-nb_errs, nb_errs, (100.*nb_errs)/nb_trys);

	printf("Exiting... (if no deadlocks...)\n");
	quit = 1;
	for (unsigned t = 0; t < nb_threads; t++) {
		pthread_join(pthread_ids[t], NULL);
	}

	free(pthread_ids);
	free(locks);
	free(recurs_count);
	free(thread_wq);

	return EXIT_SUCCESS;
}
