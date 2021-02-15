#ifndef _CSTD_INCLUDE_
#define _CSTD_INCLUDE_

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <x86intrin.h>
#include <ctype.h>
#include <time.h>
#include <limits.h>
#include <unistd.h>
#include <math.h>

/*
    Copyright (c) 2009-2020 Andrew V. Sutherland
    See LICENSE file for license details.
*/

/*
    Header file for general purpose definitions and library extensions we want to be able to use anywhere and everywhere.
*/


#ifdef DEBUG
#include <execinfo.h>
// you need to compile with -g for this to be useful, use the addr2line command line utility to convert offsets to line numbers
static inline void dump_callstack (uint32_t n)
    { void *trace[n]; size_t x; char **s = backtrace_symbols (trace, x=backtrace(trace,n));  for ( size_t i = 0 ; i < x ; i++ ) { puts(s[i]); } free (s); }
#endif

typedef __uint128_t uint128_t;

#define LONG_BITS       ((int)sizeof(long)*CHAR_BIT)

// You must define SOFTASSERTS above the inclusion of cstd.h in each source module in order to turn on softassert's
#ifdef SOFTASSERTS
#define softassert(c) assert(c)
#else
#define softassert(c)
#endif

#define _swap(a,b,w)     do{w=a;a=b;b=w;}while(0);
#define _nz(a)          (a?a:1)

static inline double get_time(void)
    { struct timeval time;  gettimeofday(&time, NULL);  return time.tv_sec + time.tv_usec / 1000000.0; }

static inline char *string_time (char buf[256])
    { time_t t = time(NULL);  strftime(buf,256,"%Y-%m-%d-%H-%M-%S",gmtime(&t)); return buf; }

#ifdef __x86_64__
static inline uint64_t get_cycles(void) { return __rdtsc(); }   // this takes something like 20 cycles
#else
static inline uint64_t get_cycles(void) { return 0; }
#endif

// units should be in KB
static inline uint64_t get_maxrss(void) { struct rusage x; return getrusage(RUSAGE_SELF,&x) == 0 ? x.ru_maxrss : 0; }

static inline uint64_t atoul (char *s) { return strtoul(s,0,10); }

// this function should be used by anyone wanting a seed for a random number generator; when debugging you can fix _cstd_seed to get deterministic behavior
unsigned long _cstd_seed;       // you can set this to any non-zero value (in your main function, not here)
static inline unsigned long cstd_seed(void)
{
    if ( ! _cstd_seed ) {
        _cstd_seed = (((unsigned long)gethostid())<<32) + getpid();     // make sure seed is different in different processes/hosts, even if seeded at (approximately) the same time
        _cstd_seed *= time(0);
    }
    return _cstd_seed;
}

#define LOG2            0.693147180559945309417232121458
#define GAMMA           0.577215664901532860606512090082

// See https://link.springer.com/article/10.1007/s10444-007-9039-2 for error analysis of our implementation of li(x)
// If we ignore errors do to precision loss, using b=2*log(x)+1 should ensure error < 1/2 for all x >= 2 (around x^(-1/3))
// Comparing with mathematica (and including errors due to precision) round(logint(x)) is on the nose for x <= 10^15, round(logintl(x)) for x <= 10^17
// For the purpose of approximating pi(x) (with an erorr of ~sqrt(x), this is way more accuracy than we need, but there isn't much benefit to truncating earlier.
// Each call takes about 500 cycles (long double version is only 10 percent slower)
static inline double logint (double x)
{
    double s, t, y, z;
    int n, b;

    if ( x <= 2 ) return 0;                     // we are only interested in approximating pi(x)
    s = t = y = log(x); z = 1; b = 2*t+1;
    for ( n = 2 ; n <= b ; n++ ) { y *= t/(2*n);  if ( (n&1) ) { z += 1.0/n; s += y*z; } else { s -= y*z; } }
    return GAMMA + log(t) + sqrt(x)*s;
}
static inline long double logintl (long double x)
{
    long double s, t, y, z;
    int n, b;

    if ( x <= 2 ) return 0;                     // we are only interested in approximating pi(x)
    s = t = y = logl(x); z = 1; b = 2*t+1;
    for ( n = 2 ; n <= b ; n++ ) { y *= t/(2*n);  if ( (n&1) ) { z += 1.0/n; s += y*z; } else { s -= y*z; } }
    return GAMMA + logl(t) + sqrtl(x)*s;
}


// The ceilbound/floorbound functions do not return ceil/floor they return upper/lower bounds that may be off by 1, but they are much faster than ceill and floorl.
// Note that these will not work properly with Valgrind!! (because Valgrind fakes long doubles using 64-bit floats)

//static inline uint64_t fastceilboundl(long double x) { union { long double ld; uint64_t i; } u; u.ld = x+0.5; u.ld += (long double)(1ul<<63); return u.i & ~(1ul<<63); }
//static inline uint64_t fastfloorboundl(long double x) { union { long double ld; uint64_t i; } u; u.ld = x-0.5; u.ld += (long double)(1ul<<63); return u.i & ~(1ul<<63); }

static inline uint64_t fastceilboundl(long double x) {  return 1+(int64_t)x; } // signed int is intentional (and faster)
static inline uint64_t fastfloorboundl(long double x) { return (int64_t)x; }   // signed int is intentional (and faster)

#define _min(a,b)       ((a)<(b)?(a):(b))       // generic min, not safe with side-effects
#define _max(a,b)       ((a)<(b)?(b):(a))       // generic max, not safe with side-effects

// Some handy utility functions
static inline uint64_t ui64_ceil_ratio (uint64_t a, uint64_t b)
    { uint64_t x = a/b; return b*x < a ? x+1 : x; }
static inline uint128_t ui128_ceil_ratio (uint128_t a, uint128_t b)
    { uint128_t x = a/b; return b*x < a ? x+1 : x; }
static inline int ui32_len (uint32_t x) { return 32-__builtin_clz(x); }
static inline int ui64_len (uint64_t x) { return 64-__builtin_clzl(x); }
static inline int ui128_len (uint128_t x) { return x>>64 ? 64+ui64_len(x>>64) : ui64_len(x); }
static inline int ui32_highbit (uint32_t x) { return 31-__builtin_clz(x); }
static inline int ui64_highbit (uint64_t x) { return 63-__builtin_clzl(x); }
static inline int ui128_highbit (uint128_t x) { return x>>64 ? 64+ui64_highbit(x>>64) : ui64_highbit(x); }
static inline int ui32_lowbit (uint32_t x) { return __builtin_ctz(x); }
static inline int ui64_lowbit (uint64_t x) { return __builtin_ctzl(x); }
static inline int ui32_v2 (uint32_t x) { return __builtin_ctz(x); }
static inline int ui64_v2 (uint64_t x) { return __builtin_ctzl(x); }
static inline int ui128_v2 (uint64_t x) { return __builtin_ctzl(x); }
static inline int ui32_wt (uint32_t x) { return __builtin_popcount(x); }
static inline int ui64_wt (uint64_t x) { return __builtin_popcountl(x); }
static inline int ui128_wt (uint128_t x) { return __builtin_popcountl((uint64_t)x) + __builtin_popcountl((uint64_t)(x>>64)); }

static inline uint64_t ui64_mod (uint64_t x, uint64_t m) { return x%m; }
static inline uint64_t i64_mod (int64_t x, uint64_t m) { if ( x >= 0 ) return ui64_mod(x,m); uint64_t t = ui64_mod((unsigned long)(-x),m);  return (t?m-t:0); }

static inline uint32_t ui32_mod (uint32_t x, uint32_t m) { return x%m; }
static inline uint32_t i32_mod (int32_t x, uint32_t m) { if ( x >= 0 ) return ui32_mod(x,m); uint32_t t = ui32_mod((unsigned long)(-x),m);  return (t?m-t:0); }

// Given za = z mod a and zb = z mod b and (1/a) mod b with a and b coprime compute z mod ab as ((a*(1/a mod b) -1)*(zb+a-za) + zb) % a*b
static inline uint64_t crt64 (uint64_t za, uint64_t a, uint64_t zb, uint64_t b, uint64_t ainv, uint64_t ab)
{
    softassert(za < a && zb < b && ainv < b && ((uint128_t)a*ainv) % b == 1);
    uint64_t u = a*ainv-1;  // note ainv < b so a*ainv < ab fits
    uint64_t z = ((uint128_t)u*(zb+a-za)+zb) % ab;
    softassert( z % a == za && z % b == zb);
    return z;
}

static inline uint64_t crt64b (uint64_t za, uint64_t a, uint64_t zb, uint64_t b, uint64_t ainv) // use when b is small and a is large
{
    softassert(za < a && zb < b && ainv < b && ((uint128_t)a*ainv) % b == 1);
    uint64_t z = za + (((zb+b-(za%b))*ainv)%b)*a;
    softassert( z % a == za && z % b == zb);
    return z;
}
static inline uint32_t crt32 (uint32_t za, uint32_t a, uint32_t zb, uint32_t b, uint32_t ainv, uint32_t ab)
{
    softassert(za < a && zb < b && ainv < b && ((uint64_t)a*ainv) % b == 1);
    uint32_t u = a*ainv-1;  // note ainv < b so a*ainv < ab fits
    uint32_t z = ((uint64_t)u*(zb+a-za)+zb) % ab;
    softassert( z % a == za && z % b == zb);
    return z;
}
static inline uint32_t crt32b (uint32_t za, uint32_t a, uint32_t zb, uint32_t b, uint32_t ainv) // use when b is small and a is large
{
    softassert(za < a && zb < b && ainv < b && ((uint64_t)a*ainv) % b == 1);
    uint32_t z = za + (((zb+b-(za%b))*ainv)%b)*a;
    softassert( z % a == za && z % b == zb);
    return z;
}
// here we require a^2*b and a*b^2 to fit in 127 bits (so 56-bit a and 24-bit b would be fine, for example)
static inline uint128_t crt64to128 (uint64_t za, uint64_t a, uint64_t zb, uint64_t b, uint64_t ainv, uint128_t ab)
{
    softassert(za < a && zb < b && ainv < b && ((uint128_t)a*ainv) % b == 1);
    softassert(2*ui64_len(a)+ui64_len(b) < 128);
    uint128_t u = a*ainv-1;  // note ainv < b so a*ainv < ab fits
    uint128_t z = (u*(zb+a-za)+zb) % ab;
    softassert( z % a == za && z % b == zb);
    return z;
}
 
// u = a*((1/a)mod b) -1, nza = a-za
static inline uint64_t fcrt64 (uint64_t u, uint64_t nza, uint64_t zb, uint64_t ab)
    { return ((uint128_t)u*(zb+nza)+zb) % ab; }
static inline uint32_t fcrt32 (uint32_t u, uint32_t nza, uint32_t zb, uint32_t ab)
    { return ((uint64_t)u*(zb+nza)+zb) % ab; }
static inline uint128_t fcrt64to128 (uint128_t u, uint64_t nza, uint64_t zb, uint128_t ab)
    { return (u*(zb+nza)+zb) % ab; }

static inline uint32_t ui32_revbit(uint32_t x)
{ 
    uint32_t n = x;
    n = ((n >> 1) & 0x55555555) | ((n << 1) & 0xaaaaaaaa);
    n = ((n >> 2) & 0x33333333) | ((n << 2) & 0xcccccccc);
    n = ((n >> 4) & 0x0f0f0f0f) | ((n << 4) & 0xf0f0f0f0);
    n = ((n >> 8) & 0x00ff00ff) | ((n << 8) & 0xff00ff00);
    n = ((n >> 16) & 0x0000ffff) | ((n << 16) & 0xffff0000);
    return n;
}

static inline uint64_t ui64_revbit(uint64_t x)
{ 
    uint64_t n = x;
    n = ((n >> 1) & 0x5555555555555555) | ((n << 1) & 0xaaaaaaaaaaaaaaaa);
    n = ((n >> 2) & 0x3333333333333333) | ((n << 2) & 0xcccccccccccccccc);
    n = ((n >> 4) & 0x0f0f0f0f0f0f0f0f) | ((n << 4) & 0xf0f0f0f0f0f0f0f0);
    n = ((n >> 8) & 0x00ff00ff00ff00ff) | ((n << 8) & 0xff00ff00ff00ff00);
    n = ((n >> 16) & 0x0000ffff0000ffff) | ((n << 16) & 0xffff0000ffff0000);
    n = ((n >> 32) & 0x0000ffffffff) | ((n << 32) & 0xffffffff00000000);
    return n;
}

// adapted from Hacker's delight, assumes x < 2^63
static inline uint64_t ui64_cbrt(uint64_t x) {
    uint64_t y, b, bs, z;
    int s = 3*(ui64_len(x)/3);

    y = 0; z = x;
    for ( ; s >= 0; s = s - 3 ) {
        y += y;
        b = 3*y*(y+1) + 1;
        bs = b << s;
        if (z >= bs && b == (bs >> s)) {
            z -= bs;
            y += 1;
        }
    }
    return (y*y*y == x ? y : 0);
}

static inline uint64_t ui64_sqrt (uint64_t x)
{
    uint64_t y, y2;
    y = (uint64_t)(sqrt(x)+0.5);
    y2 = y*y;
    if ( y2 == x ) return y;
    return 0;
}

// allow simple exponentials in string to integer conversions
static inline long atol_exp (char *str)
{
    char *s;
    long i,b,n,N;
    
    for ( s = str ; *s && *s != 'e' && *s != 'E' ; s++ );
    if ( *s ) { s++; N = b = atol (str); n = atol(s); for ( i = 1; i < n ; i++ )  N *= b; } else N = atol(str);
    return N;
}

static inline uint64_t strto64(char *str)
{
    uint64_t n;
    char buf[64];
    char *s,*t,*u;
    int e;

    if ( strlen(str)+1 > sizeof(buf) ) return 0;
    if ( (s=strchr(str,'+')) ) { if ( strchr(str,'-') ) return 0;  memcpy(buf,str,s-str); buf[s-str] = '\0'; return strto64(buf)+strto64(s+1); }
    if ( (s=strchr(str,'-')) ) { if ( strchr(str,'+') ) return 0;  memcpy(buf,str,s-str); buf[s-str] = '\0'; return strto64(buf)-strto64(s+1); }
    if ( (s=strchr(str,'*')) ) { memcpy(buf,str,s-str); buf[s-str] = '\0'; return strto64(buf)*strto64(s+1); }
    for ( s = str ; *s ; s++ ) if ( !isdigit(*s) && *s!='.' && *s != 'e' && *s != 'E' && *s != 'b' ) return 0;
    if ( str[strlen(str)-1] == 'b') { e = atoi(str); return ( e>=0 && e < 64 ? ((uint64_t)1<<e) : 0 ); }
    if ( strchr(str,'b') ) return 0;
    if ( (s=strchr(str,'e')) || (s=strchr (str,'E')) ) {
        e = atoi(s+1);
        if ( e < 0 ) return 0;
        for ( t = buf, u = str ; u < s ; u++ ) if ( isdigit(*u) ) *t++ = *u;
        *t = '\0';
        n = atoul(buf);
        if ( (t=strchr(str,'.')) ) {
            e -= strlen(buf)-(t-str);
            if ( e < 0 ) return 0;
        }
        for ( ; e > 0 ; e-- ) n *= 10;
    } else {
        n = atoul(str);
    }
    return n;
}

static inline uint32_t strto32(char *str) { uint64_t n = strto64(str); return ( n < ((uint64_t)1<<32) ? (uint32_t)n : 0 ); }


// Functions to enumerate all t-tuples of integers in [0..n-1] in lexicographic order c[t],c[t-1],...,c[1], using Knuth Alg 7.2.1.3T
// c[0] holds an auxiliary variable, combination is c[1],c[2],...,c[t], where 0 < t < n, space for 2 sentinels is also required, so c must have t+3 entries allocated
static inline void lex_combo_first (int c[], int n, int t)
    { int j;  for ( j = 1 ; j <= t ; j++ ) c[j] = j-1;  c[t+1] = n;  c[t+2] = 0;  c[0] = t; }
        
static inline int lex_combo_next (int c[], int n, int t)
{
    int j;

    if ( c[0] ) { c[c[0]] = c[0]; c[0]--; return 1; }
    if ( c[1] +1 < c[2] ) { c[1]++; return 1; }
    j = 2;  c[1] = 0;
    while ( c[j]+1 == c[j+1] ) { j++;  c[j-1] = j-2; }
    if ( j > t ) return 0;
    c[j]++;  c[0] = j-1;
    return 1;
}

#define A128_MAXSTR     "170141183460469231731687303715884105727"

// return 1 if atoi128 can be safely called without risk of overflow, 0 otherwise
static inline int atoi128validate (const char *s)
{
    const char *t;

    while (isspace(*s)) s++;
    if ( *s == '-') { s++; while (isspace(*s)); }
    for ( t = s ; isdigit(*t) ; t++ );
    if ( t-s+1 > sizeof(A128_MAXSTR) ) return 0;
    if ( t-s+1 < sizeof(A128_MAXSTR) ) return 1;
    return memcmp(s,A128_MAXSTR,t-s) < 0;
}

// like atoi, we make no attempt to detect or handle overflow
static inline __int128_t atoi128 (const char *s)
{
    __int128_t n = 0;

    while (isspace(*s)) s++;
    if (*s == '-') {
        for ( s++ ; isspace(*s) ; s++ );
        while ( isdigit(*s) ) n = 10*n + ('0' - *s++);
    } else {
        while ( isdigit(*s) ) n = 10*n + (*s++ - '0');
    }
    return n;
}

static inline uint128_t strto128(char *str)
{
    uint128_t n;
    char buf[64];
    char *s,*t,*u;
    int e;

    if ( strlen(str)+1 > sizeof(buf) ) return 0;
    if ( (s=strchr(str,'+')) ) { if ( strchr(str,'-') ) return 0;  memcpy(buf,str,s-str); buf[s-str] = '\0'; return strto128(buf)+strto128(s+1); }
    if ( (s=strchr(str,'-')) ) { if ( strchr(str,'+') ) return 0;  memcpy(buf,str,s-str); buf[s-str] = '\0'; return strto128(buf)-strto128(s+1); }
    if ( (s=strchr(str,'*')) ) { memcpy(buf,str,s-str); buf[s-str] = '\0'; return strto128(buf)*strto128(s+1); }
    for ( s = str ; *s ; s++ ) if ( !isdigit(*s) && *s!='.' && *s != '-' && *s != 'e' && *s != 'E' && *s != 'b' ) return 0;
    if ( str[strlen(str)-1] == 'b' ) { e = atoi(str); return ( e>=0 && e < 128 ? ((uint128_t)1<<e) : 0 ); }
    if ( strchr(str,'b') ) return 0;
    if ( (s=strchr(str,'e')) || (s=strchr (str,'E')) ) {
        e = atoi(s+1);
        if ( e < 0 ) return 0;
        for ( t = buf, u = str ; u < s ; u++ ) if ( isdigit(*u) ) *t++ = *u;
        *t = '\0';
        n = atoul(buf);
        if ( (t=strchr(str,'.')) ) {
            e -= strlen(buf)-(t-str);
            if ( e < 0 ) return 0;
        }
        for ( ; e > 0 ; e-- ) n *= 10;
    } else {
        n = atoi128(str);
    }
    return n;
}


static inline char *itoa128 (char buf[], __int128_t n)
{
    char c, *s, *t = buf;

    if ( ! n ) { *t++ = '0'; *t = '\0'; return buf; }
    if ( n < 0 ) { *t++ = '-'; n = -n; }
    for ( s = t ; n ; n /= 10 ) *s++ = (char) ('0' + (int)(n%10));
    *s-- = '\0';
    while ( s > t ) { c = *s; *s-- = *t; *t++ = c; }
    return buf;
}


/*
    Elementary number-theoretic functions implemented as inlines
*/
static inline uint32_t mod3(uint64_t d) { return d%3; } // trust the compiler to optimize this
static inline uint32_t mod5(uint64_t d) { return d%5; } // trust the compiler to optimize this
static inline uint32_t mod7(uint64_t d) { return d%7; } // trust the compiler to optimize this
static inline uint32_t mod9(uint64_t d) { return d%9; } // trust the compiler to optimize this

static inline int ui64_kronecker2 (uint64_t a)
    { return (a&1) ? ((a&2) ? -1 : 1) : 0; }

static inline int ui64_kronecker3 (uint64_t a)
    { int s = mod3(a); return s == 2 ? -1 : s; }

// Algorithm 1.4.10, p. 29 of [CANT] trimmed down to handle a >= 0, b > 0 odd (for the sake of space and speed)
static inline int ui64_legendre (uint64_t a, uint64_t b)
{
    uint64_t r;
    int k,v;
    
    if ( a > 2*b ) a %= b;
    while ( a >= b ) a -= b;
    k = 1;
    while ( a ) {
        v = __builtin_ctzl(a); a >>= v;
        if ( (v&1) && (b&1) && ((b&6) == 2 || (b&6) == 4) ) k = -k;
        if ( (a&b&3) == 3 ) k = -k;
        r = a;   a = (b < 2*r ? b-r : b%r);  b = r;
    }
    return ( b == 1 ? k : 0 );
}

// Algorithm 1.4.10, p. 29 of [CANT] for a,b >= 0
static inline int ui64_kronecker (uint64_t a, uint64_t b)
{
    uint64_t r;
    int k, v;
    
    if ( ! b ) return ( a==1 ? 1 : 0 );
    k = 1;
    if ( !(b&1) ) {
        if ( !(a&1) ) return 0;
        v = __builtin_ctzl(b); b >>= v;
        if ( (v&1) && ( (a&6) == 2 || (a&6) == 4 ) ) k = -1;
    }
    if ( a > b ) a %= b;
    while ( a ) {
        v = __builtin_ctzl(a); a >>= v;
        if ( (v&1) && (b&1) && ((b&6) == 2 || (b&6) == 4) ) k = -k;
        if ( (a&b&3) == 3 ) k = -k;
        r = a;   a = (b < (r+r) ? b-r : b%r);  b = r;
    }
    return ( b == 1 ? k : 0 );
}

// computes the kronecker symbol for arbitrary integers a and b
static inline int i64_kronecker (int64_t a, int64_t b)
{
    int s;
    
    if ( b < 0 ) { s = (a<0?-1:1); b = -b; } else s = 1;
    if ( a < 0 ) { long c; if ( ! b ) return (a==-1?1:0); for ( c = b ; !(c&1) ; c >>= 1 ); s *= ((c&3)==3 ? -1 : 1); a = -a; }
    return s*ui64_kronecker (a,b);
}

// uses standard Euclidean algorithm to invert a mod m.
static inline uint64_t ui64_inverse (uint64_t a, uint64_t m)
{
    uint64_t q, r, r0, r1;
    int64_t t, t0, t1;

    if ( a >= m ) a %= m;
    if ( a == 0 ) return 0;

    t1 = 1;  t0 = 0;  r0 = m;  r1 = a;
    while ( r1 > 0 ) {
        q = r0/r1;
        r = r0 - q*r1;
        r0 = r1;  r1 = r;
        t = t0 - q*t1;
        t0 = t1;  t1 = t;
    }
    if ( r0 > 1 ) return 0;
    if ( t0 < 0 ) return m - (uint64_t)(-t0);
    return (uint64_t)t0;
}

// simple Euclidean gcd, not extended
static inline uint64_t ui64_gcd (uint64_t a, uint64_t b)
{
    uint64_t q, r, r0, r1;
    
    if ( a < b ) { r0 = b;  r1 = a; } else { r0 = a; r1 = b; }
    while ( r1 > 0 ) {
        q = r0/r1;  r = r0 - q*r1;
        r0 = r1;  r1 = r;
    }
    return r0;
}
static inline uint64_t ui64_lcm (uint64_t a, uint64_t b) { return (a/ui64_gcd(a,b))*b; }

// uses standard Euclidean algorithm to invert a mod m.
static inline uint32_t ui32_inverse (uint32_t a, uint32_t m)
{
    uint32_t q, r, r0, r1;
    int32_t t, t0, t1;

    if ( a >= m ) a %= m;
    if ( a == 0 ) return 0;

    t1 = 1;  t0 = 0;  r0 = m;  r1 = a;
    while ( r1 > 0 ) {
        q = r0/r1;
        r = r0 - q*r1;
        r0 = r1;  r1 = r;
        t = t0 - q*t1;
        t0 = t1;  t1 = t;
    }
    if ( r0 > 1 ) return 0;
    if ( t0 < 0 ) return m - ((uint32_t)(-t0));
    return (uint32_t)t0;
}

// simple Euclidean gcd, not extended
static inline uint32_t ui32_gcd (uint32_t a, uint32_t b)
{
    uint32_t q, r, r0, r1;
    
    if ( a < b ) { r0 = b;  r1 = a; } else { r0 = a; r1 = b; }
    while ( r1 > 0 ) {
        q = r0/r1;  r = r0 - q*r1;
        r0 = r1;  r1 = r;
    }
    return r0;
}

static inline uint64_t ui32_lcm (uint32_t a, uint32_t b) { return ((uint64_t)a/ui32_gcd(a,b))*b; }

// simple Euclidean gcd, not extended
static inline __int128_t gcd128 (__int128_t a, __int128_t b)
{
    __int128_t q, r, r0, r1;
    
    if ( a < 0 ) a = -a;
    if ( b < 0 ) b = -b;
    if ( a < b ) { r0 = b;  r1 = a; } else { r0 = a; r1 = b; }
    while ( r1 > 0 ) {
        q = r0/r1;  r = r0 - q*r1;
        r0 = r1;  r1 = r;
    }
    return r0;
}

static inline __int128_t lcm128 (__int128_t a, __int128_t b) { return (a/gcd128(a,b))*b; }

static inline unsigned long ui_binomial (int n, int k)
{
    unsigned long a, b;
    int i;
    
    assert ( n <= 28 ); // to avoid 64-bit overflow, require n <= 28
    if ( k > n/2 ) k = n-k;
    if ( ! k ) return 1;
    for ( a = n, b=1, i = 1 ; i < k ; i++ ) { a *=(n-i);  b *= (i+1); }
    return a/b;
}

#endif
