#ifndef __INVTAB__
#define __INVTAB__

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

/*
    Functions for precomputing tables of inverses mod m.

    In each of the functions below, ptab should be an ordered list of pcnt primes that includes all prime divisors of m,
    and w should point to a buffer with space for 2m entries.  The results are written to inv.
*/

void invtab16 (uint16_t *inv, uint16_t m, uint16_t *ptab, int pcnt, uint16_t *w);
void invtab32 (uint32_t *inv, uint32_t m, uint32_t *ptab, int pcnt, uint32_t *w);

#endif