#ifndef _INCLUDE_BITMAP_
#define _INCLUDE_BITMAP_

/*
    Copyright (c) 2014,2019 Andrew V. Sutherland
    See LICENSE file for license details.
*/


/*
    Simple implementation of bitmaps, including reasonably fast functions for counting and enumerating set bits
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <memory.h>
#include "cstd.h"

typedef uint64_t *bitmap_t;

static inline uint64_t bitm (uint64_t i) { return (uint64_t)1<<(i&0x3f); }
static inline uint64_t bm_words (uint64_t n) { return (n>>6)+1; } // allocates an extra word when n is divisible by 64, but this can be useful
static inline uint64_t *_bm_alloc (uint64_t n) { return malloc(bm_words(n)*sizeof(uint64_t)); }
static inline uint64_t *bm_alloc (uint64_t n) { return calloc (bm_words(n),sizeof(uint64_t)); }
static inline void bm_free(uint64_t *bm) { free (bm); }
static inline void bm_clear(uint64_t *bm, uint64_t n) { memset (bm,0,(n>>6)*sizeof(uint64_t)); if ( (n&0x3F) ) bm[n>>6] = ~(bitm(n)-1); }
static inline void bm_erase(uint64_t *bm, uint64_t n) { memset (bm,0,bm_words(n)*sizeof(uint64_t)); }
static inline void bm_set_word(uint64_t *bm, uint64_t m, uint64_t i) { uint64_t j = i>>6, k=i&0x3f; bm[j] = ((bm[j]>>k)<<k) | (m >> k); bm[j+1] = ((bm[j]<<k)>>k) | (m<<k); }
static inline void bm_set(uint64_t *bm, uint64_t i) { bm[i>>6] |= bitm(i); }
static inline void bm_unset(uint64_t *bm, uint64_t i) { bm[i>>6] &= ~bitm(i); }
static inline int bm_test(uint64_t *bm, uint64_t i) { return (bm[i>>6] & bitm(i))!=0; }
static inline int bm_test_and_set(uint64_t *bm, uint64_t i) { uint64_t x = bm[i>>6];  uint64_t y = x | bitm(i);  bm[i>>6] = y;  return y==x; }
static inline int bm_subset (uint64_t *A, uint64_t *B, uint64_t n)
    { for ( uint64_t i = 0 ; i < bm_words(n) ; i++ ) { if ( A[i] & ~B[i] ) return 0; }  return 1; }

static inline uint64_t bm_next_set(uint64_t *bm, uint64_t m, uint64_t n)    // returns the index of the least set bit with index in [m,n), or >=n if none
{
    if ( m >= n ) return n;
    uint64_t *s = bm + (m>>6);
    uint64_t *e = bm + (n>>6);
    uint64_t x;
    
    if ( (x=(*s >> (m&0x3f))) ) return m + ui64_v2(x);
    for ( s++ ; s <= e && !*s ; s++ );
    return ((s-bm)<<6) + ui64_v2(*s);
}

// assumes bm is zero-padded to a word boundary, be sure to use bm_erase rather than bm_clear
static inline uint64_t bm_weight (uint64_t *bm, uint64_t n)
{
    uint64_t w = 0;
    for ( uint64_t *e = bm + (n>>6) ; bm <= e ; w += ui64_wt(*bm++) );
    return w;
}

#endif