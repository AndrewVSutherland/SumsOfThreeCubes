all: zcubes zcubesr zcubesv admissible

clean:
	rm -vf admissible zcubes

admissible: admissible.c
	gcc -D MAIN -g --debug -pedantic -Wall -O2 -o admissible admissible.c

zcubes: zcubes.c admissible.c primes.c invtab.c mem.c admissible.h cbrts.h primes.h mem.h invtab.h kdata.h zcheck.h report.h m64.h b32.h bitmap.h cstd.h
	gcc -pedantic -Wall -O2 -march=nehalem -o zcubes admissible.c zcubes.c invtab.c primes.c mem.c -lprimesieve -lgmp -lm -lpthread
