#ifndef _M64_INCLUDE_
#define _M64_INCLUDE_

#include <stdint.h>
#include "b32.h"
#include "cstd.h"

/*
    Copyright (c) 2017-2019 Andrew V. Sutherland
    See LICENSE file for license details.
*/

/*
    Implementation of 64-bit Montgomery modular arithmetic for odd moduli < 2^63
*/

#define SWAP(a,b)           do { typeof(a) _SWAP_TMP_ = a; a = b; b = _SWAP_TMP_; } while (0)

#define M64_STACK    4096    // number of uint64_t's we are happy to allocate on the stack

#define M64_BITS 64

// all 64-bit inputs are assumed to be in [0,p-1], where p is an odd integer in [3,2^63-1] (p need not be prime except for m64_inv_prime and sqrt/cbrt)

// computes -1/p mod 2^64 using 10-11 cycles at 3.3GHz
static inline uint64_t m64_pinv (uint64_t p)
{
    softassert (p&1 && !(p>>63));
    uint64_t t = (3*p)^12;                          // correct mod 2^4
    t *= 2+t*p; t *= 2+t*p; t *= 2+t*p;             // correct mod 2^8, 2^16, 2^32
    return t*(2+t*p);                               // correct mod 2^64
}

// returns R := 2^M64_BITS modulo p (R represents 1 in Montgomery rep), uses 4-5 cycles at 3.3GHz
static inline uint64_t m64_R (uint64_t p)
{
    softassert (p&1 && p > 2 && !(p>>63));
    uint64_t R = fastfloorboundl(18446744073709551616.0L/(int64_t)p); // for 2 < p < 2^63 this computes floor(2^64/p) exactly WILL NOT WORK WITH VALGRIND
    softassert ((R*(-p))>>1 <= p);
    for ( R *= -p ; R >= p ; R -= p );  // VALGRIND will go into an infinite loop here
    return R;
}

// computes x/R mod p.  Provided x < p*2^M64_BITS the loop will execute at most once and the total cost is 5-6 cycles
// we allow x > p*R, but if x is much larger this may be very slow
static inline uint64_t m64_redc (uint128_t x, uint64_t p, uint64_t pinv) // pinv = -1/p mod 2^64
    { uint64_t r = ((uint128_t)((uint64_t)x*pinv) * p + x) >> M64_BITS;  while ( r >= p ) r -= p;  return r; }

// computes (x*y)/R mod p (if x and y are in Montgomery rep, the output is x*y in Montgomery rep), uses 6-8 cycles
static inline uint64_t m64_mul (uint64_t x, uint64_t y, uint64_t p, uint64_t pinv)
    { return m64_redc((uint128_t)x*y,p,pinv); }

static inline uint64_t m64_sqr (uint64_t x, uint64_t p, uint64_t pinv)
    { return m64_redc((uint128_t)x*x,p,pinv); }

static inline uint64_t m64_cube (uint64_t x, uint64_t p, uint64_t pinv)
    { return m64_mul(m64_sqr(x,p,pinv),x,p,pinv); }

// computes x*y mod p, under the assumption that y*R < 2^M64_BITS (NOT VERIFIED!)
// (it will still work whenever x*y*R < 2^(2*M64_BITS), but may be very slow)
// If x is in Montgomery rep (and y is not) the returned value will be xy in Montgomery rep
static inline uint64_t m64_mul_ui (uint64_t x, uint64_t y, uint64_t R, uint64_t p, uint64_t pinv)
    { return m64_redc((uint128_t)x*y*R,p,pinv); }

// computes x*y*z/R mod p under the assumption that x*y*z < p*2^M64_BITS (NOT VERIFIED!)
// (it will still work whenever x*y*R < 2^(2*M64_BITS), but may be very slow)
// If x and y are in Montgomery rep (and z is not) the returned value will be xyz in Montgomery rep
static inline uint64_t m64_mul_mul_ui (uint64_t x, uint64_t y, uint64_t z, uint64_t p, uint64_t pinv)
    { return m64_redc((uint128_t)x*y*z,p,pinv); }

// assumes x in [0,p-1]
static inline uint64_t m64_neg (uint64_t x, uint64_t p)
    { x = p-x;  while ( x >= p ) x -= p; return x; } // while is faster than if

// assumes x,y in [0,p-1] (if not this may loop for a *very* long time)
static inline uint64_t m64_add (uint64_t x, uint64_t y, uint64_t p)
    { x += y;  while ( x >= p ) x -= p; return x; } // while is faster than if

static inline uint64_t m64_div2 (uint64_t x, uint64_t p)
    { return (x+p*(x&1))>>1; }
    
// computes x+y*z
static inline uint64_t m64_addmul (uint64_t x, uint64_t y, uint64_t z, uint64_t R, uint64_t p, uint64_t pinv)
    { return m64_redc((uint128_t)x*R+(uint128_t)y*z, p,pinv); }

// assumes x,y in [0,p-1]
static inline uint64_t m64_sub (uint64_t x, uint64_t y, uint64_t p)
    { int64_t u = x-y; while ( u < 0 ) u += p; return u; }

// Computes 2^64*n mod p (Montgomery rep of 64-bit n) for p > 2^32 given a (reasonably sharp) lower bound on floor(2^95/p)
// This takes about 16 cyclces at 3.3Ghz
static inline uint64_t m64_from_ui_bigp (uint64_t n, uint64_t p, uint64_t x)
{
    uint64_t y = ((uint128_t)n*x) >> 63;                                                                                    // lower bound on (2^32*n*x) >> 95
    uint64_t a = ((uint128_t)n << 32) - (uint128_t)y*p; softassert (a>>3 < p); while ( a >= p ) a-=p;                       // a = 2^32*n mod p
    y =  ((uint128_t)a*x) >> 63;  a = ((uint128_t)a << 32) - (uint128_t)y*p; softassert (a>>3 < p); while ( a >= p ) a-=p;  // a = 2^64*n mod p
    return (uint64_t)a;
}

// Computes 2^64*n mod p (Montgomery rep of 64-bit n) for p < 2^32 given a (reasonably sharp) lower bound on floor(2^95/p)
// This takes 15-20 cyclces at 3.3Ghz (usually 15, worst case is when p is close to 2^32 and/or n > 2^32)
static inline uint64_t m64_from_ui_smallp (uint64_t n, uint64_t p, uint64_t x)
    { softassert(!(p>>32)); return b32_red((uint64_t)b32_red((n>>32?b32_red(n,p,x):n)<<32,p,x)<<32,p,x); }

// Computes 2^64*n mod p (Montgomery rep of 64-bit n) without any precomputation
// This takes 16-20 cyclces at 3.3Ghz
static inline uint64_t m64_from_ui (uint64_t n, uint64_t p)
    { return p>>32 ? m64_from_ui_bigp(n,p,fastfloorboundl(39614081257132168794624491520.0L/(int64_t)p)) : m64_from_ui_smallp(n,p,b32_inv(p)); }

// computes 2^64*x mod p (the Montgomery representation of the integer x)
static inline uint64_t m64_from_si (int64_t x, uint64_t p)
    { return x < 0 ? m64_neg(m64_from_ui(-x,p),p) : m64_from_ui(x,p); }

// Given R=2^M64_BITS mod p (1 in Montgomery rep), computes R2=2^(2*M64_BITS) mod p (2^M64_BITS in Montgomery rep)
static inline uint64_t m64_R2 (uint64_t R, uint64_t p)
    { return m64_from_ui (R,p); }

// Given R2 = 2^128 mod p, computes 2^64*x mod p (the Montgomery representation of the integer x), faster than m64_from_ui once R2 is precomputed, only 6-8 cycles
static inline uint64_t m64_from_ui_R2 (uint64_t x, uint64_t R2, uint64_t p, uint64_t pinv)
    { return m64_mul (x,R2,p,pinv); }

// Given R2 = 2^128 mod p, computes 2^64*x mod p (the Montgomery representation of the integer x), slightly faster than m64_from_si
static inline uint64_t m64_from_si_R2 (int64_t x, uint64_t R2, uint64_t p, uint64_t pinv)
    { return x < 0 ? m64_neg(m64_from_ui_R2(-x,R2,p,pinv),p) : m64_from_ui_R2(x,R2,p,pinv); }

// given R2=R^2 mod p, computes R3=R^3 mod p (R3 represents R2 in Montgomery rep)
static inline uint64_t m64_R3 (uint64_t R2, uint64_t p, uint64_t pinv)
    { return m64_sqr(R2,p,pinv); }
 
// computes x/R mod p (the integer represented by x in Montgomery rep)
static inline uint64_t m64_to_ui (uint64_t x, uint64_t p, uint64_t pinv)
    { return m64_redc(x, p, pinv); }

// computes x/R mod p (the integer represented by x in Montgomery rep)
static inline int64_t m64_to_si (uint64_t x, uint64_t p, uint64_t pinv)
    { return (int64_t)m64_redc(x, p, pinv); }

// simple right-left binary exp is faster than 2-bit fixed window
static inline uint64_t m64_exp_ui (uint64_t x, uint64_t e, uint64_t R, uint64_t p, uint64_t pinv)
{
    uint64_t y;

    if (!e) return R;
    for (;!(e&1);e>>=1) x = m64_sqr(x,p,pinv);
    for (y=x,e>>=1;e;e>>=1) {
        x = m64_sqr(x,p,pinv);
        if ( (e&1) ) y = m64_mul(x,y,p,pinv);
    }
    return y;
}

static inline uint64_t m64_exp_2k (uint64_t x, int k, uint64_t p, uint64_t pinv)
    {  while ( k-- ) x = m64_sqr (x, p, pinv); return x; }

// sets y[i] = x^(2^i) for 0 <= i <= e
static inline uint64_t *m64_pow_2k (uint64_t y[], uint64_t x, int k, uint64_t R, uint64_t p, uint64_t pinv)
    { y[0] = R; if (!k) return y; y[1] = x; for ( int i = 2 ; i <= k ; i++ ) { y[i] = m64_sqr(y[i-1],p,pinv); } return y; }

// given x=aR mod p computes R/a mod p (Montgomery inverse)
static inline uint64_t m64_inv_small (uint64_t r, uint64_t R2, uint64_t R3, uint64_t p, uint64_t pinv)
{
    uint64_t s, t, v;
    int k;
    
    // using __builtin_ctzl is slower for p < 256, but give almost a 50% speedup when p ~ 2^60

    assert (r); k = 0;
    while ( !(r&1) ) { r >>= 1; k++; }
    t = (p-r)>>1;  v = 1; s = 2; k++;
    while ( !(t&1) ) { t >>= 1; s <<= 1; k++; }
    for (;;) {
        if ( t > r ) {
            t = (t-r)>>1; v += s; s <<= 1; k++;
            while ( !(t&1) ) { t >>= 1; s <<= 1; k++; }
        } else {
            r = (r-t)>>1; s += v; v <<= 1; k++;
            if ( ! r ) break;
            while ( !(r&1) ) { r >>= 1; v <<= 1; k++; }
        }
    }
    while ( v >= p ) v -= p;
    v = p - v; // note that v is not zero
    // we could use a lookup table for this, but the improvment is minimal (typically under 1 nanosecond)
    if ( k <= M64_BITS ) { v = m64_redc((uint128_t)v*R3,p,pinv); k += M64_BITS; } else { v = m64_redc((uint128_t)v*R2,p,pinv); }
    return m64_redc((uint128_t)v*(((uint64_t)1)<<(2*M64_BITS-k)),p,pinv);
}

// given x=aR mod p computes R/a mod p (Montgomery inverse)
static inline uint64_t m64_inv (uint64_t r, uint64_t R2, uint64_t R3, uint64_t p, uint64_t pinv)
{
    uint64_t s, t, v;
    int b,k;
    
    if ( p < 1787 ) return m64_inv_small(r,R2,R3,p,pinv);    // crossover is CPU dependent, this was tested on Intel Xeon E5/E7 v2 and v3
    
    assert (r);
    b = __builtin_ctzl(r); r >>= b;
    t = (p-r)>>1;  v = 1; s = 2; k = b+1;
    b = __builtin_ctzl(t); t >>= b; s <<= b; k+=b;
    do {
        if ( t > r ) {
            t = (t-r)>>1; v += s; s <<= 1; k++;
            b = __builtin_ctzl(t); t >>= b; s <<= b; k+=b;   // updating s and k twice is slightly faster
        } else {
            r = (r-t)>>1; s += v; v <<= 1; k++;
            if ( ! r ) break;
            b = __builtin_ctzl(r); r >>= b; v <<= b; k+=b;
        }
    } while ( r);
    while ( v >= p ) v -= p;
    v = p - v; // note that v is not zero
    // we could use a lookup table for this, but the improvment is minimal (typically under 1 nanosecond)
    if ( k <= M64_BITS ) { v = m64_redc((uint128_t)v*R3,p,pinv); k += M64_BITS; } else { v = m64_redc((uint128_t)v*R2,p,pinv); }
    return m64_redc((uint128_t)v*(((uint64_t)1)<<(2*M64_BITS-k)),p,pinv);
}

// this is somewhat faster than m64_inv
static inline uint64_t m64_invprime (uint64_t r, uint64_t R, uint64_t p, uint64_t pinv)
    { return m64_exp_ui (r, p-2, R, p, pinv); }

// computes y[i] = m64_inv(x[i]) for i from 0 to n-1, y and x may coincide
static inline void m64_inv_array (uint64_t y[], uint64_t x[], int n, uint64_t R, uint64_t R2, uint64_t R3, uint64_t p, uint64_t pinv)
{
    uint64_t c[M64_STACK];
    uint64_t u, v;
    int i;

    if ( n > M64_STACK ) {
        for ( i = 0 ; i+M64_STACK < n ; i += M64_STACK ) m64_inv_array(y+i,x+i,M64_STACK,R,R2,R3,p,pinv);
        y += i;  x += i;  n-= i;
    }
    if ( n <= 0 ) return;
    
    c[0] = x[0];
    for ( i = 1 ; i < n ; i++ ) c[i] = m64_mul (c[i-1],x[i],p,pinv);
    u = m64_inv (c[n-1],R2,R3,p,pinv);
    for ( i = n-1 ; i > 0 ; i-- ) { v = m64_mul (c[i-1],u,p,pinv); u = m64_mul (u,x[i],p,pinv); y[i] = v; } // set y[i] after reading x[i] in case x=y
    y[0] = u;
}

// computes y[i] = m64_inv(x[i]) for i from 0 to n-1, y and x may coincide
static inline void m64_invprime_array (uint64_t y[], uint64_t x[], int n, uint64_t R, uint64_t p, uint64_t pinv)
{
    uint64_t c[M64_STACK];
    uint64_t u, v;
    int i;

    if ( n > M64_STACK ) {
        for ( i = 0 ; i+M64_STACK < n ; i += M64_STACK ) m64_invprime_array(y+i,x+i,M64_STACK,R,p,pinv);
        y += i;  x += i;  n-= i;
    }
    if ( n <= 0 ) return;
    
    c[0] = x[0];
    for ( i = 1 ; i < n ; i++ ) c[i] = m64_mul (c[i-1],x[i],p,pinv);
    u = m64_invprime (c[n-1],R,p,pinv);
    for ( i = n-1 ; i > 0 ; i-- ) { v = m64_mul (c[i-1],u,p,pinv); u = m64_mul (u,x[i],p,pinv); y[i] = v; } // set y[i] after reading x[i] in case x=y
    y[0] = u;
}

// given x[i] = x^(2^i) for i in [1..floor(log_2(e))] and e in [0,..2^64-1], computes x^e
static inline uint64_t m64_exp_pow (uint64_t x[], uint64_t e, uint64_t R, uint64_t p, uint64_t pinv)
{
    uint64_t y;
    uint64_t m;
    
    switch (e) {
    case 0: return R;
    case 1: return x[0];
    case 2: return x[1];
    case 3: return m64_mul(x[0],x[1],p,pinv);
    case 4: return x[2];
    case 5: return m64_mul(x[0],x[2],p,pinv);
    case 6: return m64_mul(x[1],x[2],p,pinv);
    case 7: return m64_mul(m64_mul(x[0],x[1],p,pinv),x[2],p,pinv);
    case 8: return x[3];
    case 9: return m64_mul(x[0],x[3],p,pinv);
    case 10: return m64_mul(x[1],x[3],p,pinv);
    }
    for ( m = 1 ; !(e&m) ; m <<= 1, x++ );
    y = *x++;
    for ( m <<= 1 ; m <= e ; m <<= 1, x++ ) if ( (e&m) ) y = m64_mul(y,*x,p,pinv);
    return y;
}
// computes the Legendre symbol (x/p)
static inline uint64_t m64_legendre (uint64_t x, uint64_t R, uint64_t p, uint64_t pinv)
    { return x ? (m64_exp_ui(x,p>>1,R,p,pinv) == R ? 1 : -1) : 0; }

// Sets rr to cuberoots of a modulo the odd prime p < 2^63 and returns their number
static inline int m64_cbrts (uint64_t rr[3], uint64_t a, uint64_t R, uint64_t p, uint64_t pinv)
{
    uint64_t b, r, x, y, z, b3, z3;
    uint64_t m;
    int d, e;

    if ( p == 3 || !a ) { rr[0] = a; return 1; }

    m = (p-1)/3;
    if ( 3*m+1 != p ) { // p mod 2 case
        m = 2*m+1;      // m = (2*p-1)/3, so (a^m)^3 = a^(2p-1) = a^p*a^(p-1) = a
        rr[0] = m64_exp_ui (a,m,R,p,pinv);
        return 1;
    }
    // write p = 3^e*m+1
    for ( e = 1 ; mod3(m) == 0 ; e++, m/= 3 );
    r = m64_exp_ui (a,((3-mod3(m))*m-2)/3,R,p,pinv);           // r = a^((3-(m%3))m-2)/3), r^3 = a^m * a^(-2) or a^(2m) * a^(-2)
    b = m64_mul(m64_sqr(a,p,pinv),m64_cube(r,p,pinv),p,pinv);  // b = a^m or a^(2m)=(a^m)^2 is in the 3-Sylow
    r = m64_mul (r,a,p,pinv);                                  // r^3 = b * a, we just need to multiply r by b^(-1/3)

    // we have a 2/3 chance of b having maximal order (hence no cube root of b), so check this first
    for ( d = 0, y = b3 = b ; d < e-1 && y != R ; d++ ) { b3 = y; y = m64_cube(y,p,pinv); }
    if ( y != R ) return 0; // no cube root

    // at this point b has order 3^d < 3^e and thus has a cube root
    if ( d==0 && (p&3)==3) { 
        // if b == 1 we have r^3=a, we just need a primitive cube root of unity z3=(-1+sqrt(-3))/2
        // when p = 3 mod 4 we can compute this quickly, so we may as well do so.
        x = m64_add(R,m64_add(R,R,p),p);
        z = m64_exp_ui (x,(p+1)>>2,R,p,pinv);
        z3 = m64_div2(m64_sub(z,R,p),p);
    } else {
        z3 = 0;
        // We know that b = a^m has non-trivial order 3^i < 3^e, we need an element g of the 3-Sylow with order at least 3^(i+1)
        // A random element will give us such an r with probability at least 2/3, so we expect 1.5 exponentiations, on average
        x = m64_add(R,R,p);  // start with 2
        z = m64_exp_ui(x,m,R,p,pinv);
        for ( e = 0, y = z ; y != R ; e++ ) { z3 = y; y = m64_cube(y,p,pinv); }
        if ( e <= d ) {
            uint64_t two = x;   // loop over odd numbers > 1 (we could skip composites but we expect one of 3,5,7 to work)
            for ( x = m64_add(x,R,p) ;; x = m64_add(x,two,p) ) {
                z = m64_exp_ui(x,m,R,p,pinv);
                for ( e = 0, y = z ; y != R ; e++ ) { z3 = y; y = m64_cube(y,p,pinv); }
                if ( e > d ) break;
            }
        }
        softassert(z3);
        // at this point we know that b has order 3^d and z has order 3^e > 3^d
        if ( d ) while ( e > d+1 ) { z = m64_cube(z,p,pinv);  e--; }
        while ( d > 1 ) {
            // Here z has order 3^(d+1) and b has order 3^d, so either z^3 = b or (z^2)^3 = b
            y = m64_cube(z,p,pinv);
            r = m64_mul(r,z,p,pinv);
            b = m64_mul (b,y,p,pinv);
            if ( b3 == z3 ) {
                r = m64_mul(r,z,p,pinv);
                b = m64_mul (b,y,p,pinv);
            }
            // Here b has order at most 3^(e-2), compute its new order 3^d
            for ( d = 0, y = b ; d < e-1 && y != R ; d++ ) { b3 = y; y = m64_cube(y,p,pinv); }
            // Adjust z to have order 3^(d+1)
            if ( d ) while ( e > d+1 ) { z = m64_cube(z,p,pinv);  e--; }
        }
        if ( d == 1 ) r = m64_mul(r,(m64_cube(z,p,pinv) == b ? m64_sqr(z,p,pinv) : z),p,pinv);
    }
    rr[0] = r;
    rr[1] = r = m64_mul(r,z3,p,pinv);
    rr[2] = m64_mul(r,z3,p,pinv);
    return 3;
}

// Check if a (in Montgomery rep) has a cuberoot modulo the odd prime p < 2^63
static inline int m64_has_cbrts (uint64_t a, uint64_t R, uint64_t p, uint64_t pinv)
{
    uint64_t b, r, y;
    uint64_t m;
    int d, e;

    if ( !a || mod3(p) != 1 ) return 1;
    for ( m = (p-1)/3, e = 1 ; mod3(m) == 0 ; e++, m/= 3 );
    r = m64_exp_ui (a,((3-mod3(m))*m-2)/3,R,p,pinv);           // r = a^((3-(m%3))m-2)/3), r^3 = a^m * a^(-2) or a^(2m) * a^(-2)
    b = m64_mul(m64_sqr(a,p,pinv),m64_cube(r,p,pinv),p,pinv);  // b = a^m or a^(2m)=(a^m)^2 is in the 3-Sylow
    r = m64_mul (r,a,p,pinv);                                  // r^3 = b * a, we just need to multiply r by b^(-1/3)
    for ( d = 0, y = b ; d < e-1 && y != R ; d++ ) y = m64_cube(y,p,pinv);
    return ( y == R );
}

#endif