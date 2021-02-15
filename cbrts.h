#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include "primes.h"
#include "invtab.h"
#include "b32.h"
#include "m64.h"
#include "mem.h"
#include "cstd.h"

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

/*
    This module precomputes cuberoots modulo prime powers (at least up to sqrt(dmax)) and modulo smallish products of prime powers that may appears as cofactors.
    Lookup functions are provided for retrieving cached cuberoots.  The main interfaces are

        * cached_cuberoots_mod_q -- this function returns cuberoots modulo a specified prime power
        * cdentry -- given an admissible d and a prime d returns a pointer x into a table of cofactor data such that x->d*d <= max and x->d is (p-1)-smooth
                     caller can then work down the table from there (but approx 1/2 the entries below the returned entry need not be (p-1)-smooth)
                     each entry identifies the largest prime dividing x->d and a list of cuberoots mod x->d (see struct cdrec below)
        * sdentry/sdtab -- for smaller d (<= SDMAX) we also cache precomputed inverses, currenty zcubes accesses sdtab directly rather than calling sdentry

    All the datatructures in this module are precomputed and then shared (read-only)
*/

// Regardless of the setting of SDMAX and CDMAX below we always cache cuberoots of all prime powers that can appear in a cofactor of d
// (meaning coprime to the largest prime divisor of d), which means up to min(sqrt(dmax),dmax/pmin)

#define CPMIN   512     // We always cache primes up to CPMIN which needs to be at at least 127 and as big as the largest prime divisor of k
#define SDMAX   (1<<12) // Limits d for which we will cache inverses (we need 2d bytes of space per admissible d < SDMAX, which we would like in L2)
#define CDMAX   (1<<26) // Limits d for which we will cache cuberoots (we need 12+4n bytes for each admissible d < CDMAX with n cuberoots
                        // The number of admissible d is rho_d*dmax/log(dmax)^(1/3), which is roughly dmax/6 or so in the range of interest


static inline uint64_t Q2cuberoot(uint64_t a)
{
    uint64_t x,y,t;

    x = a+2*((a^(a+a))&4);  // correct mod 16
    y = 3;                  // y = 1/(3x^2) to at least half precision
    for (unsigned i=0 ; i < 4 ; i++) {
        t = x*x;
        y *= 2-3*t*y;       // update y to current precision
        y *= 2-3*t*y;       // update y to double precision
        x = (2*x*t+a)*y;    // iterate x --> (2x^3+a)/3x^2
    }
    softassert(x*x*x == a);
    return x;
}

static inline int verify_cuberoot (uint64_t r, uint64_t k, uint64_t d) { uint128_t z = r; return ( (z*((z*z)%d)%d) == k%d ); }

static inline int has_cuberoots_modp (uint64_t k, uint64_t p)
    { return mod3(p)==2 || m64_has_cbrts(m64_from_ui(k,p),m64_R(p),p,m64_pinv(p)); }

static inline uint32_t cuberoots_modp (uint64_t r[3], uint64_t k, uint64_t p)
{
    unsigned i, n;

    uint64_t pinv = m64_pinv(p);
    uint64_t R = m64_R(p);
    n = m64_cbrts(r,m64_from_ui(k,p),R,p,pinv);
    for ( i = 0 ; i < n ; i++ ) { r[i] = m64_to_ui(r[i],p,pinv); softassert (verify_cuberoot(r[i],k,p)); }
    return n;
}


// computes the cube roots of k modulo p^e, where p is a prime, p^e < 2^63 and returns the number of cuberoots (0,1,3)
// for k = 0 mod p or p==3 we require e = 1
static uint32_t cuberoots_modq (uint64_t r[3], uint64_t k, uint64_t p, uint32_t e)
{
    uint64_t s[3],t,R,R2,pinv,q,qinv,two,a;
    unsigned i,j,n;

    if ( p==2 ) { if ( (k&1) ) { r[0] = Q2cuberoot(k) & ((1UL<<e)-1); return 1; } else { assert (e==1); r[0] = 0; return 1; } }
    pinv = m64_pinv(p);  R = m64_R(p);
    a = m64_from_ui(k,p);
    if ( ! a ) { assert(e==1); r[0] = 0; return 1; }
    n = m64_cbrts (r,a,R,p,pinv);
    if ( !n ) return 0;
    if ( e == 1 ) { for ( int i = 0 ; i < n ; i++ ) { r[i] = m64_to_ui(r[i],p,pinv); softassert(verify_cuberoot(r[i],k,p)); } return n; }
    assert (p!=3);

    // compute inverses of 3x^2 mod p
    for ( i = 0 ; i < n ; i++ ) { s[i] = m64_sqr(r[i],p,pinv); s[i] = m64_add(s[i],m64_add(s[i],s[i],p),p); }   // s[i] = 3*r[i]^2 mod p
    m64_invprime_array (s,s,n,R,p,pinv);
    
    for ( q = p, i = 1 ; i < e ; i++ ) q *= p;
    qinv = m64_pinv(q);  R = m64_R(q);  two = m64_add(R,R,q); R2 = m64_R2(R,q);

    // switch modulus from p to q
    for ( i = 0 ; i < n ; i++ ) { r[i] = m64_from_ui_R2(m64_to_ui(r[i],p,pinv),R2,q,qinv); s[i] = m64_from_ui_R2(m64_to_ui(s[i],p,pinv),R2,q,qinv); }

    a = m64_from_ui(k,q);
    for ( i = 0 ; i < n ; i++ ) {
        uint64_t x = r[i], y = s[i];                                                // x = cbrt(k) mod p, y = 1/(3x^2) mod p (stored mod q)
        for ( j = 1 ; j < e ; j <<= 1 ) {                                           // hensel our way up, doubling precision with each step
            x = m64_sub(x,m64_mul(m64_sub(m64_cube(x,q,qinv),a,q),y,q,qinv),q);     // x <- x - (x^3-k)*y mod q
            t = m64_sqr(x,q,qinv);  t = m64_add(t,m64_add(t,t,q),q);                // t = 3x^2 mod q
            y = m64_mul(y,m64_sub(two,m64_mul(t,y,q,qinv),q),q,qinv);               // y <- y*(2-3*x^2*y) mod q
        }
        r[i] = m64_to_ui(x,q,qinv);
        softassert (verify_cuberoot(r[i],k,q));
    }
    return n;
}

static uint32_t cpmax;          // all p <= cpmax that are admissible divisors of d and prime to k are listed in cptab
static uint64_t cqmax;          // we store cuberoots of k mod p^e <= cqmax = dmax/pmin for each p in cptab
static uint32_t *cptab;         // list of primes p <= cpmax that are admissible divisors of d prime to k, first prime is at offset 1
static uint32_t *cprtab;        // list of offsets into crdata (in low 29 bits), bit 31 set if n=3 cuberoots (else n=1)
                                // the ith cuberoot of k mod cptab[j]^e is stored in crdata[crtab[j]+n*(e-1)+i]
static uint32_t cpcnt;          // # primes listed in cptab and cprtab (each has size cpcnt+1 offset 0 is null)
static uint32_t *cqroots;       // cuberoots of k mod p^e for p < sqrt(dmax) and p^e < dmax/pmin, 32 bits for p > sqrt(cqmax)
static uint32_t cp64maxpi;      // for i <= cp64max crtab[i] points to 64-bits values (used only for p <= cbrt(dmax)), above 64max we use 32 bit values

static void precompute_cuberoots_modq (uint32_t k, uint64_t pmin, uint64_t pmax, uint64_t dmax)
{
    primes_ctx_t *ctx;
    uint64_t p,q;
    uint64_t cp64max, bytes, mem=0;
    uint64_t r[3];
    uint32_t next, cpsize, cprsize, kp;
    int e,i,j,n;

    assert (goodk(k));
    report_timer_reset ();
    ctx = primes_enum_start (1,k);
    for ( kp = k ; (p=primes_enum_next(ctx)) <= k ; ) { while ( !(kp%p) ) { kp /= p; } if ( kp == 1 ) break; }
    primes_enum_end (ctx);
    kp = p;   softassert (!(k%p));                                      // kp = largest prime factor of p
    cpmax = (uint32_t)_min(pmax,ceil(sqrt(dmax)));                      // p <= min(pmax,sqrt(dmax)) includes all primes that can appear in a cofactor of d
    if ( cpmax < CPMIN ) cpmax = CPMIN;                                 // we want all p < 128 we might want for z-testing
    if ( cpmax < kp ) cpmax = kp;                                       // and all p | k
    cqmax = _max(cpmax,ui64_ceil_ratio(dmax,pmin));                     // q <= min(cpmax,dmax/pmin) includes all prime powers that can appear in a cofactor of d
    cp64max = cqmax >= (1UL<<32) ? _min(cpmax,ceil(sqrt(cqmax))) : 0;   // for p <= cp64pmax q=p^e may require 64 bits so we store all cuberoots as 64-bit ints
    cpsize = primes_pi_bound(cpmax);                                    // this is typically twice as large as we need, we realloc at the end
    cprsize = 1 + 3 * (primes_pi_power_bound(cpmax,cqmax) + primes_pi_power_bound(cp64max,cqmax));  // also larger than we need, we will realloc later
    assert (cprsize < (1<<30));
    cptab = private_malloc (cpsize*sizeof(*cptab));
    cprtab = private_malloc (cpsize*sizeof(*cprtab));
    cqroots = private_malloc (cprsize*sizeof(*cqroots));
    cptab[0] = cprtab[0] = cqroots[0] = 0;
    next = 1;                                                           // start at offset 1, offset 0 is used for null (so cptab[1] holds the firsst prime)
    cpcnt = kpcnt = 0;
    ctx = primes_enum_start (1,cpmax);
    while ( (p=primes_enum_next(ctx)) <= cpmax ) {
        if ( p==3 || (p <= k && !(k%p)) ) continue;                     // we don't cache cuberoots mod powers of 3 or p|k, these are handled separately
        assert (next < cprsize);
        for ( e = 1, q = p ; (uint128_t)q*p <= cqmax ; e++, q *= p );
        n = cuberoots_modq (r,k,p,e);
        if ( !n ) continue;
        assert (n==1 || n==3);
        cptab[++cpcnt] = p;
        cprtab[cpcnt] = next | (((uint32_t)n-1)<<30);
        if ( p > cp64max ) {
            assert ( !(q>>32) );            // all cached cuberoots must fit in 32 bits here
            assert (next+e*n < cprsize);
            // each mod q operation below typically takes less than 20 cycles, probably not worth trying to optimize
            for ( i = 0, q = p ; i < e-1 ; i++, q*= p ) for ( j = 0 ; j < n ; j++ ) cqroots[next++] = (uint32_t)(r[j]%q);
            for ( j = 0 ; j < n ; j++ ) cqroots[next++] = (uint32_t)r[j];
        } else {
            assert (next+2*e*n < cprsize);
            cp64maxpi = cpcnt;
            // as above, each mod q operation below typically takes less than 20 cycles, probably not worth trying to optimize
            for ( i = 0, q = p ; i < e-1 ; i++, q*= p ) for ( j = 0 ; j < n ; j++ ) { *((uint64_t *)(cqroots+next)) = r[j]%q; next += 2; };
            for ( j = 0 ; j < n ; j++ )  { *((uint64_t *)(cqroots+next)) = r[j]; next += 2; };
        }
    }
    primes_enum_end(ctx);
    cprtab[cpcnt+1] = next;
    assert (cpcnt+1 <= cpsize && cpcnt+2 <= cpsize && next <= cprsize);
    cptab = shared_realloc_private (cptab, cpsize*sizeof(*cptab), bytes=(cpcnt+1)*sizeof(*cptab));  mem += bytes;
    cprtab = shared_realloc_private (cprtab, cpsize*sizeof(*cptab), bytes=(cpcnt+2)*sizeof(*cprtab)); mem += bytes;
    cqroots = shared_realloc_private (cqroots, cprsize*sizeof(*cptab), bytes=next*sizeof(*cqroots));  mem += bytes;
    report_printf ("Precomputed %u cuberoots of k modulo powers of %u primes (cpmax=%u, cqmax=%lu, cp64maxpi=%u) in %.1fs using %.1f MB shared memory\n",
                   next-1, cpcnt, cpmax, cqmax, cp64maxpi, report_timer_elapsed(), (double)mem/(1<<20));
}


// returns index of greatest prime <= p in cptab such that p*d <= dmax
static inline unsigned pimaxp (uint64_t p, uint64_t d, uint64_t dmax)
{
    uint128_t dd = d;   // used to avoid integer division (worth it)
    unsigned low, hi, mid;

    low = 0; hi = cpcnt+1;
    while ( hi-low > 1 ) {
        mid = low + (hi-low)/2;
        if ( cptab[mid] <= p && dd*cptab[mid] <= dmax ) low = mid; else hi = mid;
    }
    return low;
}

// return the largest index i <= mapi such that cptab[i]*d <= dmax
static inline unsigned pimaxpi (unsigned pi, uint64_t d, uint64_t dmax)
{
    uint128_t dd = d;   // used to avoid integer division (worth it)
    unsigned low, hi, mid;

    softassert (pi<=cpcnt);
    low = 0; hi = pi+1;
    while ( hi-low > 1 ) {
        mid = low + (hi-low)/2;
        if ( dd*cptab[mid] <= dmax ) low = mid; else hi = mid;
    }
    return low;
}

// returns the largest e such that we have cached cuberoots mod p^e, where p=cptab[pi]
static inline unsigned cached_cuberoots_e (unsigned pi)
{
    softassert (pi<=cpcnt);
    uint32_t *x = cprtab+pi;
    unsigned e = ((*(x+1)&0x7FFFFFFFU)-(*x&0x7FFFFFFFU));
    assert(e>0);
    if ( *x>>31 ) e /= 3;
    if ( pi <= cp64maxpi ) e /= 2;
    return e;
}

// returns number of cuberoots mod p=cptab[pi] (1 or 3)
static inline unsigned cached_cuberoots_n (unsigned pi)
{
    softassert (pi>0&&pi<=cpcnt);
    return 1+2*(cprtab[pi]>>31);
}

// returns a pointer to start of array of cached cuberoots mod powers of p=cptab[i]
// this is a list of e lists of n cuberoots of 32 or 64 bits (the former for p > cp64max, otherwise the latter)
static inline uint32_t *cached_cuberoots_r (unsigned pi)
{
    softassert (pi>0&&pi<=cpcnt);
    return cqroots + (cprtab[pi] & 0x7FFFFFFFU);
}

// sanity check called only when VERIFY is defined
static inline unsigned verify_cuberoots_modpie (uint64_t r[3], unsigned n, unsigned pi, unsigned e)
{
    softassert (pi>0&&pi<=cpcnt);
    uint64_t q = cptab[pi];
    for ( unsigned i = 1 ; i < e ; i++ ) q *= cptab[pi];
    for ( unsigned i = 0 ; i < n ; i++ ) if ( ! verify_cuberoot (r[i], K, q) ) return 0;
    return 1;
}

// grabs cached cuberoots mod p^e, where p=cptab[pi], and returns their number (1 or 3)
static inline int cached_cuberoots_modq (uint64_t r[3], unsigned pi, unsigned e)
{
    softassert (pi > 0 && pi <= cpcnt);
    softassert (e > 0 && e <= cached_cuberoots_e(pi));
    int n = cached_cuberoots_n(pi);
    if ( pi > cp64maxpi ) {
        uint32_t *rp = cached_cuberoots_r(pi) + n*(e-1);
        *r++ = (uint64_t) (*rp++);
        if ( n != 1 ) { *r++ = (uint64_t) (*rp++); *r++ = (uint64_t) (*rp++); }
        softassert (verify_cuberoots_modpie (r-n,n,pi,e));
    } else {
        uint64_t *rp = (uint64_t*) cached_cuberoots_r(pi) + n*(e-1);
        *r++ = *rp++;
        if ( n != 1 ) { *r++ = *rp++; *r++ = *rp++; }
        softassert (verify_cuberoots_modpie (r-n,n,pi,e));
    }
    return n;
}

static inline uint64_t power (uint64_t p, uint64_t e)
    { uint64_t q = p; for ( int i = 1 ; i < e ; i++ ) { q *= p; } return q; }

// returns the inverse of d mod q=p^e (computes inverse mod p then hensel lifts)
static inline uint64_t modqinv(uint64_t d, uint64_t q, uint64_t p, unsigned e)
{
    uint64_t pinv,R;
    uint64_t x,y,two,qinv;

    softassert (q==power(p,e));
    if ( !(q&1) ) return q-(m64_pinv(d) & (q-1));

    pinv = m64_pinv(p);  R = m64_R(p);
    x = m64_to_ui(m64_invprime(m64_from_ui(d,p),R,p,pinv),p,pinv);
    softassert (((uint128_t)x*d)%p == 1);
    if ( e==1 ) return x;
    qinv = m64_pinv(q); R = m64_R(q); two = m64_add(R,R,q);
    x = m64_from_ui(x,q);  y = m64_from_ui(d,q);
    for ( e-- ; e ; e >>= 1 ) x = m64_mul(x,m64_sub(two,m64_mul(x,y,q,qinv),q),q,qinv);     // x <- x(2 - xy) mod q
    x = m64_to_ui(x,q,qinv);
    softassert (((uint128_t)x*d)%q == 1);
    return x;
}

// Cached precomputed data for cpmax-smooth admissible d <= cdmax <= CDMAX < 2^32 coprime to k
static uint32_t cdmax;          // all cpmax-smooth admissible d <= cdmax coprime to k are listed in cdtab
static uint64_t cdmin;          // dmax/cdmax
static struct cdrec {           // record for each d
    uint32_t d;                 // d <= cdmax coprime to k
    uint32_t p;                 // largest prime divisor of d
    uint32_t r;                 // offset into cdroots where n cuberoots of k mod d are stored
    uint16_t n;                 // number of cuberoots of k mod d (at most 3^7 = 2187 for 32-bit d coprime to k)
    uint16_t sdpi;              // index into sdtab for d <= sdmask
} *cdtab[16];                   // entry zero is reserved for null in each table
static uint32_t cdcnt[16];      // cdcnts[i] is the number of entries in cdtab[i], starting from offset 1 (so cdcnt[i]+1 entries total)
static uint32_t cdmaxp[16];     // cdtab[i] contains all cdmaxp[i]-smooth d <= cdmax
static uint32_t *cdroots;       // cuberoots of k mod d for d in cdtab

// Cached precomputed data for cpmax-smooth admissible d <= sdmax <= SDMAX < 2^16 coprime to k
static uint32_t sdmax;          // all cpmax-smooth admissible d <= sdmax coprime to k are listed in sdtab
static uint64_t sdmin;          // sdmax/sdmin
static struct sdrec {           // record fo r each d
    uint16_t d;                 // d <= sdmax coprime to k
    uint16_t p;                 // largest prime divisor of d
    uint16_t r;                 // offset into sdroots (duplicates cdroots, but 16-bit values, improves memory locality)
    uint16_t n;                 // number of cuberoots of k mod d (at mosst 3^4 = 81 for 16-bit d coprime to k)
    uint64_t dinv;              // 2^64/d, used for Barret reduction mod d
    uint32_t i;                 // offset into sdinvs containing list of inverses mod d
} *sdtab;                       // entry zero is reserved for null
static uint16_t sdcnt;          // number of entries in sdtab starting from offset 1 (so sdcnt+1 entries total)
static uint16_t *sdroots;       // cuberoots of k mod d for d in sdtab (duplicates cdroots but we use 16-bits here for memory locality)
static uint16_t *sdinvs;        // inverses mod d  for d in sdtab (total # entries is the sum of d in sdtab)

// used to sort cdtab by p below
static int ui32_cmp1 (const void *a, const void *b)
    { return *((uint32_t*)a+1) < *((uint32_t*)b+1) ? -1 : ( *((int32_t*)a+1) > *((int32_t*)b+1) ? 1 : 0 ); }

// This could be made faster by batching inversions, but it takes very little time as is (a few seconds for cmax=10^8 which already uses 300MB)
static void precompute_cuberoots_modd (uint32_t k,uint64_t pmin, uint64_t pmax, uint64_t dmax)
{
    uint128_t dd;
    struct cdrec *x, *y;
    uint64_t z[3], bytes, mem=0;
    uint32_t p[9], q[9], d[9], c[9], r[9];
    uint32_t *rr;
    uint32_t next, w, nroots, ninvs;
    int e[9], pi[9];
    int i, j, n, zc;

    report_timer_reset();

    cdmax = _min(ui64_ceil_ratio(dmax,pmin),sqrt(dmax));    // default is to cache all possible cofactors (divisors of d coprime to its largest prime factor)
    if ( cdmax > CDMAX ) cdmax = CDMAX;                     // but we impose a cap CDMAX to keep memory manageable
    if ( cdmax < CPMIN ) cdmax = CPMIN;                     // to avoid annoying special cases we make cdmax at least min(cpmax) so we are at least caching something
    cdmin = ui64_ceil_ratio(dmax,cdmax);                    // for p >= cdmin any d divisible by p will have its cofactor cached
    sdmax = _min(cdmax,SDMAX);                              // for d up to SDMAX we also cache inverses mod d (in a table of length d indexed by a mod d)
    assert ( sdmax > 2 );                                   // this ensures we won't call b32_inv with modulus 2
    sdmin = ui64_ceil_ratio(dmax,sdmax);                    // for p >= sdmin any d divisible by p will have inverses mod its cofactor
    assert (cdmax <= cqmax);                                // sanity check that we have already cached all the prime powers we need
    cdtab[0] = private_malloc (cdmax*sizeof(*cdtab[0]));    // more space than needed, we will realloc later
    cdroots = private_malloc (3*cdmax*sizeof(*cdroots));    // this should be more than enough space, but we will verify this as we go
    memset(cdtab[0],0,sizeof(*cdtab[0]));
    cdcnt[0] = 0; next = 0;
    pi[n=0] = pimaxp (cdmax,1,cdmax);
    assert(pi[n]);
    d[n] = q[n] = p[n] = cptab[pi[n]]; e[n] = 1;
    for(;;) {
        zc = cached_cuberoots_modq (z,pi[n],e[n]);  assert (zc);
        x = cdtab[0] + ++cdcnt[0];
        x->d = d[n]; x->p = p[0];
        x->r = r[n] = next;
        rr = cdroots + r[n];
        if ( n ) {
            uint64_t u = (uint64_t)d[n-1]*modqinv(d[n-1],q[n],p[n],e[n]) - 1;
            for ( i = 0 ; i < c[n-1] ; i++ ) {
                uint64_t nza = d[n-1]-cdroots[r[n-1]+i];
                for ( j = 0 ; j < zc ; j++ ) *rr++ = fcrt32(u,nza,z[j],d[n]);
            }
        } else {
            for ( j = 0 ; j < zc ; j++ ) *rr++ = (uint32_t)z[j];
        }
        c[n] = x->n = rr - (cdroots+x->r);
        next += c[n];
        assert (next <= 3*cdmax);
        for ( i = 0 ; i < x->n ; i++ ) softassert(verify_cuberoot(cdroots[x->r+i], k, d[n]));   // this should compile to nothing if SOFTASSERTS are off

        // increase exponent if we can
        if ( (dd = (uint128_t)d[n]*p[n]) <= cdmax ) { e[n]++; q[n] *= p[n]; d[n] = (uint64_t)dd; continue; }
        // add a new prime if we can
        if ( (i = pimaxpi(pi[n]-1,d[n],cdmax)) ) {
            pi[++n] = i;
            q[n] = p[n] = cptab[pi[n]]; e[n] = 1; d[n] = d[n-1]*p[n];
            continue;
        }
        // if we are at the min prime we have to remove it
        if ( pi[n] == 1 ) { n--; if ( n < 0 ) break; }
        // reduce current exponent, decrease current prime if exponent hits 0
        if ( ! --e[n] ) {
            pi[n]--; q[n] = p[n] = cptab[pi[n]]; e[n] = 1; d[n] = n ? d[n-1]*p[n] : p[n];
            continue;
        }
        // we reduced the current exponent and are going to add a new prime (which must fit), we need to reset r[n] before doing so
        // search backwards through the table to find the value of r[n] we need (for d = d[n]/p[n]), this is a bit of hack but faster than recomputing
        while ( x >= cdtab[0] && p[n]*x->d != d[n] ) x--;
        assert ( x >= cdtab[0] );
        d[n] = x->d; r[n] = x->r;
        for (q[n] = p[n], i = 1 ; i < e[n] ; q[n] *= p[n], i++ );    // remultiply rather than dividing
        // add the next smaller prime (at this point it must fit)
        n++;
        pi[n] = pi[n-1]-1; q[n] = p[n] = cptab[pi[n]]; e[n] = 1; d[n] = d[n-1]*p[n];
    }
    assert (cdcnt[0] < cdmax);
    cdroots = shared_realloc_private (cdroots, 3*cdmax*sizeof(*cdroots), bytes=next*sizeof(*cdroots));  mem += bytes;
    cdtab[0] = shared_realloc_private (cdtab[0], cdmax*sizeof(*cdtab[0]), bytes=(cdcnt[0]+1)*sizeof(*cdtab[0]));  mem += bytes;

    // Sort by smoothness first, so we can bisect by smoothness
    qsort (cdtab[0]+1,cdcnt[0],sizeof(*cdtab[0]),ui32_cmp1);

    // Repeatedly bisect cdtab[0] according to smoothness to create cdtab[1], cdtab[2], ..., up to 15 tables
    cdmaxp[0] = cdmax;
    for ( i = 1 ; i < 15 ; i++ ) {
        if ( cdcnt[i-1] <= 32 ) break;  // stop when the table gets small
        j = cdcnt[i-1]/2;
        w = cdtab[0][j].p;
        if ( cdtab[0][j+1].p == w ) { w--; while ( cdtab[0][j].p >= w ) j--; }
        assert (j);
        cdcnt[i] = j;
        cdmaxp[i] = w;
        assert (cdtab[0][j+1].p > w && cdtab[0][j].p <= w);
    }
    cdcnt[i] = 0;   // zero terminate the list of tables

    // Now resort by d in preparation for populating bisected tables
    qsort (cdtab[0]+1,cdcnt[0],sizeof(*cdtab[0]),ui32_cmp);

    // Create sdtab before populating bisected tables so sdpi values will get copied
    // Use a binary search to find the largest d in cdtab[0] with d <= sdmax
    int low = 0, hi = cdcnt[0]+1;
    x = cdtab[0];
    while ( hi-low > 1 ) {
        int mid = low + (hi-low)/2;
        if ( x[mid].d <= sdmax ) low = mid; else hi = mid;
    }
    sdcnt = low;

    sdtab = shared_malloc (bytes=(sdcnt+1)*sizeof(*sdtab));  mem += bytes;
    memset(sdtab,0,sizeof(*sdtab));
    for ( i = 1, j = n = 0 ; i <= sdcnt ; i++ ) {
        sdtab[i].d = cdtab[0][i].d;  sdtab[i].p = cdtab[0][i].p; sdtab[i].n = cdtab[0][i].n;
        n += sdtab[i].n; j += sdtab[i].d;
    }
    for ( i = 1 ; i <= sdcnt ; i++ ) cdtab[0][i].sdpi = i;
    sdroots = shared_malloc (bytes=n*sizeof(*sdroots));  mem += bytes;
    sdinvs = shared_malloc (bytes=j*sizeof(*sdinvs));  mem += bytes;

    // make a copy of small primes (we want a table of uint16_t's to pass to invtab16)
    for ( i = 1 ; i < cpcnt && cptab[i] <= sdmax ; i++ );
    uint16_t spcnt = i;
    uint16_t *sptab = malloc (spcnt*sizeof(*sptab));
    for ( i = 0 ; i < spcnt ; i++ ) sptab[i] = cptab[i+1];

    uint16_t *tmp = malloc (2*_max(k,sdmax)*sizeof(*tmp));
    nroots=0, ninvs=0;
    for ( i = 1 ; i <= sdcnt ; i++ ) {
        sdtab[i].r = nroots; nroots += sdtab[i].n;
        for ( j = 0 ; j < sdtab[i].n ; j++ ) sdroots[sdtab[i].r+j] = (uint16_t)cdroots[cdtab[0][i].r+j];
        sdtab[i].dinv = sdtab[i].d > 2 ? b32_inv (sdtab[i].d) : (uint64_t)1<<63;    // don't call b32_inv for d=2, compute 2^64/2 ourselves
        sdtab[i].i = ninvs; ninvs += sdtab[i].d;
        invtab16 (sdinvs+sdtab[i].i, sdtab[i].d, sptab, spcnt, tmp);
    }
    free (sptab);
    // Now create smoothness bisected lookup tables
    for ( i = 1 ; cdcnt[i] ; i++ ) {
        cdtab[i] = shared_malloc (bytes = (cdcnt[i]+1)*sizeof(*cdtab[i]));  mem += bytes;
        memset (cdtab[i],0,sizeof(*cdtab[i]));
        for ( x = cdtab[i-1]+cdcnt[i-1], y = cdtab[i]+cdcnt[i] ; x > cdtab[i-1] ; x-- ) if ( x->p <= cdmaxp[i] ) *y-- = *x;
        assert (y==cdtab[i]);
    }
    free (tmp);

    // The next two lines should compile into nothing when SOFTASSERTS is not set
    for ( i = 1 ; i <= cdcnt[0] ; i++ ) for ( j = 0 ; j < cdtab[0][i].n ; j++ ) softassert(verify_cuberoot(cdroots[cdtab[0][i].r+j],K,cdtab[0][i].d));
    for ( i = 1 ; i <= sdcnt ; i++ ) for ( j = 0 ; j < sdtab[i].n ; j++ ) softassert(verify_cuberoot(sdroots[sdtab[i].r+j],K,sdtab[i].d));

    report_printf ("Precomputed %u zr modulo %u d <= %u and inverses modulo %u d <= %u in %.1fs, using %.1fMB shared memory\n",
                    next, cdcnt[0], cdmax, report_timer_elapsed(), sdcnt, sdmax, (double)mem/(1<<20));
}

// returns pointer to maximal entry with d*x->d <= dmax and (p-1)-smooth (but not all entries below this are necessarily p-smooth, caller must check)
static inline struct cdrec *cdentry (uint64_t p, uint64_t d, uint64_t dmax)
{
    uint128_t dd = d;
    struct cdrec *x;
    unsigned i,low,mid,hi;

    softassert (dd*cdmax >= dmax);
    if ( dd*cdtab[0][1].d > dmax ) return 0;
    for ( i = 0 ; cdcnt[i] && cdmaxp[i] >= p ; i++ );
    if ( i ) i--;
    x = cdtab[i];
    low = 0; hi = cdcnt[i]+1;
    while ( hi-low > 1 ) {
        mid = low + (hi-low)/2;
        if ( dd*x[mid].d <= dmax ) low = mid; else hi = mid;
    }
    while ( x[low].p > p ) low--;   // note x[0].p == 0
    return low ? x+low : 0;
}

static void precompute_cuberoots  (int k, uint64_t pmin, uint64_t pmax, uint64_t dmax)
{
    precompute_cuberoots_modq (k, pmin, pmax, dmax);    // caches cuberoots of all powers of p up to qmax=min(dmax/pmin,sqrt(dmax)
    precompute_cuberoots_modd (k, pmin, pmax, dmax);    // caches cuberoots of all d up to min(qmax,CDMAX)
}
