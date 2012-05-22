CPPFLAGS += -D_GNU_SOURCE
CFLAGS += -W -Wall -std=c99
LDFLAGS += -lpthread

all: lockarena

clean:
	rm -f lockarena *.o
