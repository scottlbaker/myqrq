
CC=gcc
CFLAGS:=-D PA -pthread -I.

LDFLAGS:=$(LDFLAGS) -lpthread -lpulse-simple -lpulse -lncurses
OBJECTS=qrq.o pulseaudio.o

all: qrq

qrq: $(OBJECTS)
	$(CC) -Wall -o $@ $^ -lm $(LDFLAGS)

.c.o:
	$(CC) -Wall $(CFLAGS) -c $<

install: qrq
	cp qrq $(DESTDIR)/bin/

uninstall:
	rm -f $(DESTDIR)/bin/qrq

clean:
	rm -f qrq *.o
