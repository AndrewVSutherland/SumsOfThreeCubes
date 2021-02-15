#ifndef _INCLUDE_BM_INCLUDE_
#define _INCLUDE_BM_INCLUDE_

#include "bitmap.h"
#include "cstd.h"

/*
    Copyright (c) 2019 Andrew V. Sutherland
    See LICENSE file for license details.
*/

/*
    Implementation of 32-bit Barrett modular arithmetic
*/

// We require m>2 in b32_inv (we don't handle 2 because it adds a clock cycle to a time critical function); all other functions will handle m>1
// Computes floor(2^64/m) (exactly, even though fastfloorboundl is used), uses 3 cycles at 3.3GHz
static inline uint64_t b32_inv (uint32_t m) 
    { softassert(m>2); return fastfloorboundl(18446744073709551616.0L/(int64_t)m); }

static inline uint32_t b32_red (uint64_t a, uint32_t m, uint64_t minv) 
    { softassert(m>1 && minv); uint64_t q = ((uint128_t)a * minv) >> 64; softassert((a-q*m)>>1 < m); a -= q*m; while ( a >= m ) a -= m; return a; }

static inline uint32_t b32_mul (uint32_t a, uint32_t b, uint32_t m, uint64_t minv)
    { return b32_red ((uint64_t)a*b, m, minv); }

static inline uint32_t b32_sqr (uint32_t a, uint32_t m, uint64_t minv)
    { return b32_red ((uint64_t)a*a, m, minv); }

static inline uint32_t b32_cube (uint32_t a, uint32_t m, uint64_t minv)
    { return b32_mul (a, b32_sqr(a,m,minv), m, minv); }

// returns a+b*c mod m
static inline uint32_t b32_addmul (uint32_t a, uint32_t b, uint32_t c, uint32_t m, uint64_t minv)
    { return b32_red (a+(uint64_t)b*c, m, minv); }

static inline uint32_t b32_add (uint32_t a, uint32_t b, uint32_t m)
    { softassert(a<m && b<m); uint64_t c = (uint64_t)a+b; while ( c >= m ) c-=m; return c; }

static inline uint32_t b32_sub (uint32_t a, uint32_t b, uint32_t m)
    { softassert(a<m && b<m); uint64_t c = (uint64_t)a+m-b; while ( c >= m ) c-=m; return c; }

static inline uint32_t b32_neg (uint32_t a, uint32_t m)
    { softassert(a<m); return a ? m-a : 0; }

// given za mod b and 1/a mod b, returns the unique c < b for which za + c*a < a*b is congruent to za mod a and zb mod b (where a < 2^64, b < 2^32, ab < 2^96)
static inline uint32_t b32_crt_multiplier (uint32_t zb, uint32_t b, uint32_t zab, uint32_t ainvb, uint64_t binv)
    { return b32_mul(zb+b-zab,ainvb,b,binv); }

// lifts (za mod a, zb mod b) to (z mod ab) with a < 2^64, b < 2^32, ab < 2^64
static inline uint64_t b32_crt64 (uint64_t za, uint64_t a, uint32_t zb, uint32_t b, uint32_t ainvb, uint64_t binv)
{
    softassert(!(((uint128_t)a*b) >> 64));
    softassert(za < a && zb < b && ainvb < b && (a*ainvb) % b == 1 && b32_mul(b32_red(a,b,binv),ainvb,b,binv) == 1);
    uint64_t z = za + b32_crt_multiplier(zb,b,b32_red(za,b,binv),ainvb,binv)*a;
    softassert( z % a == za && z % b == zb && z < a*b);
    return z;
}

// lifts (za mod a, zb mod b) to (z mod ab) with a < 2^64, b < 2^32, ab < 2^96
static inline uint128_t b32_crt96 (uint64_t za, uint64_t a, uint32_t zb, uint32_t b, uint32_t ainvb, uint64_t binv)
{
    softassert(za < a && zb < b && ainvb < b && (a*ainvb) % b == 1 && b32_mul(b32_red(a,b,binv),ainvb,b,binv) == 1);
    uint128_t z = za + b32_crt_multiplier(zb,b,b32_red(za,b,binv),ainvb,binv)*(uint128_t)a;
    softassert( z % a == za && z % b == zb);
    return z;
}

static inline uint32_t b32_div2 (uint32_t x, uint32_t p)
    { softassert(p&1); return (x+p*(x&1))>>1; }


// given bitmasks zam of residues mod a and zbm of residues mod b, with a,b < 64 coprime and ainvb = 1/a mod b and binv = 2^64/b
// compute bitmap m of length a*b with zth bit set if the (z mod a)th bit of zam is set and the (z mod b)th bit of zbm is set
// m should have space for a*b bits (so length (a*b)>>6 + 1)
static inline uint64_t *b32_crtmap64 (uint64_t m[], uint64_t am, uint32_t a, uint64_t bm, uint32_t b, uint32_t ainvb, uint64_t binv)
{
    int na=ui64_wt(am), nb=ui64_wt(bm);
    uint32_t w[na], x[na], y[nb];
    uint32_t r;
    int i, j;

    softassert (a && a < 64 && !(am>>a) && b && b < 64 && !(bm>>b) && b32_mul(a,ainvb,b,binv)==1);
    bm_clear(m,a*b);
    for ( i = j = 0 ; am ; i++, am>>=1 ) if ( (am&1) ) { w[j] = i; x[j] = b32_neg(b32_mul(i,ainvb,b,binv),b); j++; }
    for ( i = j = 0 ; bm ; i++, bm>>=1 ) if ( (bm&1) ) { y[j] = b32_mul(i,ainvb,b,binv); j++; }
    // this is about 8 times faster than using b32_64
    for ( i = 0 ; i < na ; i++ ) for ( j = 0 ; j < nb ; j++ ) { r = x[i] + y[j]; if ( r >= b ) r -= b; bm_set (m,w[i]+r*a); }
    return m;
}

// same as b32_crtmap64 except with 3 coprime moduli a,b,c < 64
static inline uint64_t *b32_crt3map64 (uint64_t m[], uint64_t am, uint32_t a, uint64_t bm, uint32_t b, uint64_t cm, uint32_t c, uint32_t ainvb, uint64_t binv, uint32_t abinvc, uint64_t cinv)
{
    int na=ui64_wt(am), nb=ui64_wt(bm), nc=ui64_wt(cm);
    uint32_t w[na], x[na], y[nb], z[nc];
    uint32_t ab = a*b;
    uint32_t r;
    int i, j, k;

    softassert (a < 64 && !(am>>a) && b < 64 && !(bm>>b) && c < 64 && !(cm>>c) && b32_mul(a,ainvb,b,binv)==1 && b32_mul(b32_red(ab,c,cinv),abinvc,c,cinv)==1);
    bm_clear(m,ab*c);
    for ( i = j = 0 ; am ; i++, am>>=1 ) if ( (am&1) ) { w[j] = i; x[j] = b32_neg(b32_mul(i,ainvb,b,binv),b); j++; }
    for ( i = j = 0 ; bm ; i++, bm>>=1 ) if ( (bm&1) ) { y[j] = b32_mul(i,ainvb,b,binv); j++; }
    for ( i = j = 0 ; cm ; i++, cm>>=1 ) if ( (cm&1) ) { z[j] = b32_mul(i,abinvc,c,cinv); j++; }
    for ( i = 0 ; i < na ; i++ ) {
        for ( j = 0 ; j < nb ; j++ ) {
            r = x[i] + y[j]; if ( r >= b ) r -= b;
            uint32_t u = w[i]+r*a, v = b32_neg(b32_red(u*abinvc,c,cinv),c);
            for ( k = 0 ; k < nc ; k++ ) {
                r = v + z[k]; if ( r >= c ) r -= c;
                bm_set (m,u+r*ab);
            }
        }
    }

    return m;
}

// same as b32_crtmap64 except now a,b < 128 and bitmaps are 128-bits
static inline uint64_t *b32_crtmap128 (uint64_t m[], uint128_t am, uint32_t a, uint128_t bm, uint32_t b, uint32_t ainvb, uint64_t binv)
{
    int na=ui128_wt(am), nb=ui128_wt(bm);
    uint32_t w[na], x[na], y[nb];
    uint32_t r;
    int i, j;

    softassert (a < 128 && !(am>>a) && b < 128 && !(bm>>b) && b32_mul(a,ainvb,b,binv)==1);
    bm_clear(m,a*b);
    for ( i = j = 0 ; am ; i++, am>>=1 ) if ( (am&1) ) { w[j] = i; x[j] = b32_neg(b32_mul(i,ainvb,b,binv),b); j++; }
    for ( i = j = 0 ; bm ; i++, bm>>=1 ) if ( (bm&1) ) { y[j] = b32_mul(i,ainvb,b,binv); j++; }
    for ( i = 0 ; i < na ; i++ ) for ( j = 0 ; j < nb ; j++ ) { r = x[i] + y[j]; if ( r >= b ) r -= b; bm_set (m,w[i]+r*a); }

    return m;
}

// same as b32_crtmap128 except with 3 coprime moduli a,b,c < 128
static inline uint64_t *b32_crt3map128 (uint64_t m[], uint128_t am, uint32_t a, uint128_t bm, uint32_t b, uint128_t cm, uint32_t c, uint32_t ainvb, uint64_t binv, uint32_t abinvc, uint64_t cinv)
{
    int na=ui128_wt(am), nb=ui128_wt(bm), nc=ui128_wt(cm);
    uint32_t w[na], x[na], y[nb], z[nc];
    uint32_t ab = a*b;
    uint32_t r;
    int i, j, k;

    softassert (a < 128 && !(am>>a) && b < 128 && !(bm>>b) && c < 128 && !(cm>>c) && b32_mul(a,ainvb,b,binv)==1 && b32_mul(b32_red(ab,c,cinv),abinvc,c,cinv)==1);
    bm_clear(m,ab*c);
    for ( i = j = 0 ; am ; i++, am>>=1 ) if ( (am&1) ) { w[j] = i; x[j] = b32_neg(b32_mul(i,ainvb,b,binv),b); j++; }
    for ( i = j = 0 ; bm ; i++, bm>>=1 ) if ( (bm&1) ) { y[j] = b32_mul(i,ainvb,b,binv); j++; }
    for ( i = j = 0 ; cm ; i++, cm>>=1 ) if ( (cm&1) ) { z[j] = b32_mul(i,abinvc,c,cinv); j++; }
    for ( i = 0 ; i < na ; i++ ) {
        for ( j = 0 ; j < nb ; j++ ) {
            r = x[i] + y[j]; if ( r >= b ) r -= b;
            uint32_t u = w[i]+r*a, v = b32_neg(b32_red(u*abinvc,c,cinv),c);
            for ( k = 0 ; k < nc ; k++ ) {
                r = v + z[k]; if ( r >= c ) r -= c;
                bm_set (m,u+r*ab);
            }
        }
    }
    return m;
}

// same as b32_crtmap64 except now a,b can be anything up to 2^31
static inline uint64_t *b32_crtmap (uint64_t m[], uint64_t *am, uint32_t a, uint64_t *bm, uint32_t b, uint32_t ainvb, uint64_t binv)
{
    int na=bm_weight(am, a), nb=bm_weight(bm, b);
    uint32_t *w, *x, *y;
    uint32_t r;
    int i, j;

    softassert (!(a>>31) && !(b>>31));
    // don't allocate on the stack, we have no idea how big these might be
    w = malloc(na*sizeof(*w)); x = malloc(na*sizeof(*x)); y = malloc(nb*sizeof(*y));
    bm_clear(m,a*b);
    for ( i = j = 0 ; (i = bm_next_set(am,i,a)) < a ; j++ ) { w[j] = i; x[j] = b32_neg(b32_mul(i,ainvb,b,binv),b); }
    assert (j==na);
    for ( i = j = 0 ; (i = bm_next_set(bm,i,b)) < b ; j++ ) y[j] = b32_mul(i,ainvb,b,binv);
    assert (j==nb);
    for ( i = 0 ; i < na ; i++ ) for ( j = 0 ; j < nb ; j++ ) { r = x[i] + y[j]; if ( r >= b ) r -= b; bm_set (m,w[i]+r*a); }
    free (w); free(x); free(y);
    return m;
}

// simple binary exp  (faster than 2-bit sliding window)
static inline uint32_t b32_exp_ui (uint32_t x, uint64_t e, uint32_t p, uint64_t pinv)
{
    uint32_t y;

    if (!e) return 1;
    for (;!(e&1);e>>=1) x = b32_sqr(x,p,pinv);
    for (y=x,e>>=1;e;e>>=1) {
        x = b32_sqr(x,p,pinv);
        if ( (e&1) ) y = b32_mul(x,y,p,pinv);
    }
    return y;
}

// Sets rs to cuberoots of a modulo the odd prime p < 2^63 and returns their number
static inline int b32_cbrts (uint32_t rr[3], uint32_t a, uint32_t p, uint64_t pinv)
{
    uint32_t b, r, x, y, z, b3, z3;
    uint32_t m;
    int d, e;

    softassert (p&1);
    if ( p == 3 || !a ) { rr[0] = a; return 1; }

    m = (p-1)/3;
    if ( 3*m+1 != p ) { // p mod 2 case
        m = 2*m+1; // m = (2*p-1)/3;
        // note (a^m)^3 = a^(2p-1) = a^p*a^(p-1) = a
        rr[0] = b32_exp_ui (a,m,p,pinv);
        softassert(b32_cube(rr[0],p,pinv)==a);
        return 1;
    }
    // write p = 3^e*m+1
    for ( e = 1 ; mod3(m) == 0 ; e++, m/= 3 );
    r = b32_exp_ui (a,((3-mod3(m))*m-2)/3,p,pinv);               // r = a^((3-(m%3))m-2)/3), r^3 = a^m * a^(-2) or a^(2m) * a^(-2)
    b = b32_mul(b32_sqr(a,p,pinv),b32_cube(r,p,pinv),p,pinv);   // b = a^m or a^(2m)=(a^m)^2 is in the 3-Sylow
    r = b32_mul (r,a,p,pinv);                                   // r^3 = b * a, we just need to multiply r by b^(-1/3)

    // we have a 2/3 chance of b having maximal order (hence no cube root of b), so check this first
    for ( d = 0, y = b3 = b ; d < e-1 && y != 1 ; d++ ) { b3 = y; y = b32_cube(y,p,pinv); }
    if ( y != 1 ) return 0; // no cube root

    // at this point b has order 3^d < 3^e and thus has a cube root
    if ( d==0 && (p&3)==3) { 
        // if b == 1 we have r^3=a, we just need a primitive cube root of unity z3=(1+sqrt(-3))/2
        // when p = 3 mod 4 we can compute this quickly, so we may as well do so.
        z = b32_exp_ui (3,(p+1)>>2,p,pinv);
        z3 = b32_div2(b32_sub(z,1,p),p);
    } else {
        // We know that b = a^m has non-trivial order 3^i < 3^e, we need an element g of the 3-Sylow with order at least 3^(i+1)
        // A random element will give us such an r with probability at least 2/3, so we expect 1.5 exponentiations, on average
        z = b32_exp_ui(2,m,p,pinv);
        for ( e = 0, y = z ; y != 1 ; e++ ) { z3 = y; y = b32_cube(y,p,pinv); }
        if ( e <= d ) {
            for ( x = 3 ;; x = b32_add(x,2,p) ) {
                z = b32_exp_ui(x,m,p,pinv);
                for ( e = 0, y = z ; y != 1 ; e++ ) { z3 = y; y = b32_cube(y,p,pinv); }
                if ( e > d ) break;
            }
        }
        // at this point we know that b has order 3^d and z has order 3^e > 3^d
        if ( d ) while ( e > d+1 ) { z = b32_cube(z,p,pinv);  e--; }
        while ( d > 1 ) {
            // Here z has order 3^(d+1) and b has order 3^d, so either z^3 = b or (z^2)^3 = b
            y = b32_cube(z,p,pinv);
            r = b32_mul(r,z,p,pinv);
            b = b32_mul (b,y,p,pinv);
            if ( b3 == z3 ) {
                r = b32_mul(r,z,p,pinv);
                b = b32_mul (b,y,p,pinv);
            }
            // Here b has order at most 3^(e-2), compute its new order 3^d
            for ( d = 0, y = b ; d < e-1 && y != 1 ; d++ ) { b3 = y; y = b32_cube(y,p,pinv); }
            // Adjust z to have order 3^(d+1)
            if ( d ) while ( e > d+1 ) { z = b32_cube(z,p,pinv);  e--; }
        }
        if ( d == 1 ) r = b32_mul(r,(b32_cube(z,p,pinv) == b ? b32_sqr(z,p,pinv) : z),p,pinv);
    }
    softassert (z3!=1 && b32_cube(z3,p,pinv)==1);
    softassert (b32_cube(r,p,pinv)==a);
    rr[0] = r;
    rr[1] = r=b32_mul(r,z3,p,pinv);
    rr[2] = b32_mul(r,z3,p,pinv);
    return 3;
}
#endif