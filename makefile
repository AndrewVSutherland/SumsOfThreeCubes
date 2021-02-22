all: zcubes

clean:
	rm -vf zcubes

zcubes: zcubes.c admissible.c primes.c invtab.c mem.c admissible.h cbrts.h primes.h mem.h invtab.h kdata.h zcheck.h report.h m64.h b32.h bitmap.h cstd.h
	gcc -pedantic -Wall -O2 -march=nehalem -o zcubes admissible.c zcubes.c invtab.c primes.c mem.c -lprimesieve -lgmp -lm -lpthread
