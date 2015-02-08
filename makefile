# A basic makefile for building compiled scheme files
all: out.c
	gcc -g -Wall -o out out.c

clean:
	rm *.o out
