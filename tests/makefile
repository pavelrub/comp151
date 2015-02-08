CC=gcc
CFLAGS=-g -Wall -w -I/home/pavelr/Documents/comp151/final_project
SRCS = $(wildcard *.c)
PROGS = $(patsubst %.c,%,$(SRCS))

all: $(PROGS)

%: %.c
	$(CC) $(CFLAGS) -o $@ $<

clean:
	rm $(PROGS)
