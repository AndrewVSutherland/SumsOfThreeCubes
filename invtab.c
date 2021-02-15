#include <assert.h>
#include "b32.h"
#include "cstd.h"
#include "invtab.h"

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

// sets inv[i] to 1/i mod n for i in (Z/nZ)* and 0 ow
// ptab should point to a sorted list of pcnt primes known to contain all the prime divisors of n, and w should point to buffer of length 2*n
void invtab16 (uint16_t *inv, uint16_t n, uint16_t *ptab, int pcnt, uint16_t *w)
{
    uint64_t ninv;
    uint16_t *g = w, *gi = w+n;
    uint32_t x;
    uint32_t i,j,m,p;

    assert (n > 1);

    // set inv[j] to j for j in (Z/nZ)^* and 0 ow
    inv[0] = 0; for ( j = 1 ; j < n ; j++ ) inv[j] = 1;
    for ( i = 0 ; i < pcnt && (p=ptab[i]) <= n/2 ; i++ ) if ( !(n%p) ) for ( j = p ; j < n ; j += p ) inv[j] = 0;

    // enumerate (Z/nZ)^*
    ninv = b32_inv(n);
    for ( j = 1, m = 0 ; j < n ; j++ ) if ( inv[j] ) g[m++] = j;
    gi[0] = 1; for ( j = 1 ; j < m ; j++ ) gi[j] = b32_red(gi[j-1]*g[j],n,ninv);
    
    x = ui32_inverse(gi[m-1],n);
    assert (x);

    for ( j = m-1 ; j > 0 ; j-- ) { gi[j] = b32_red(x*gi[j-1],n,ninv); x = b32_red(x*g[j],n,ninv); }
    for ( j = 0 ; j < m ; j++ ) {  softassert ((g[j]*gi[j])%n == 1); inv[g[j]] = gi[j]; }
}

// sets inv[i] to 1/i mod n for i in (Z/nZ)* and 0 ow
// ptab should point to a sorted list of pcnt primes known to contain all the prime divisors of n, and w should point to buffer of length 2*n
void invtab32 (uint32_t *inv, uint32_t n, uint32_t *ptab, int pcnt, uint32_t *w)
{
    uint64_t ninv;
    uint32_t *g = w, *gi = w+n;
    uint64_t x;
    uint32_t i,j,m,p;

    assert (n > 1);

    // set inv[j] to j for j in (Z/nZ)^* and 0 ow
    inv[0] = 0; for ( j = 1 ; j < n ; j++ ) inv[j] = 1;
    for ( i = 0 ; i < pcnt && (p=ptab[i]) <= n/2 ; i++ ) if ( !(n%p) ) for ( j = p ; j < n ; j += p ) inv[j] = 0;

    // enumerate (Z/nZ)^*
    ninv = b32_inv(n);
    for ( j = 1, m = 0 ; j < n ; j++ ) if ( inv[j] ) g[m++] = j;
    gi[0] = 1; for ( j = 1 ; j < m ; j++ ) gi[j] = b32_red((uint64_t)gi[j-1]*g[j],n,ninv);
    
    x = ui32_inverse(gi[m-1],n);
    assert (x);

    for ( j = m-1 ; j > 0 ; j-- ) { gi[j] = b32_red(x*gi[j-1],n,ninv); x = b32_red(x*g[j],n,ninv); }
    for ( j = 0 ; j < m ; j++ ) {  softassert (((uint64_t)g[j]*gi[j])%n == 1); inv[g[j]] = gi[j]; }
}
