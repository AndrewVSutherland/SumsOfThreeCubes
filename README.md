# SumsOfThreeCubes

This repo contains a C implementation of the algorithm described in the paper [On a question of Mordell](https://arxiv.org/abs/2007.01209) by Andrew R. Booker and Andrew V. Sutherland

It uses the [primesieve](https://github.com/kimwalisch/primesieve) and [GMP](https://gmplib.org/) libraries which need to be installed before you can build the software in this repo.

To build just type `make`.

To search for for solutions to x^3 + y^3 + z^3 = k for cubefree k = +/- 3 mod 9 with |z| <= zmax, d := |x+y| <= dmax, and largest prime divisor p of d in [pmin,pmax] using n threads running in parallel, type

    ./zcubes n k pmin pmax dmax zmax
    
 For example
 
    ./zcubes 8 57 1 1e9 1e9 1e10
 
 will output 15 solutions for k=57 with d <= 10^9 and |z| <= 10^10 using 8 threads in about 10 seconds (YMMV).

