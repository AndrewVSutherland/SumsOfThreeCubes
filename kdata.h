#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include "admissible.h"
#include "invtab.h"
#include "b32.h"
#include "mem.h"
#include "cstd.h"

/*
    This module performs k-specific precomputation, including creating tables of admissible z for d mod 27k and precomputing data used when lifting
    arithmetic progressions modulo divisors of 54k.

    We will always try to crt/lift mod one of 9, 18, 63, 81, 126, or 162 (at most 4 of these, depending on k) without increasing the number of progresssions.
    Depending on how much room there is between d and zmax we will lift modulo larger divisors of 54k in order to take advantage of cubic reciprocity.

    Everything in this module is precomputed and then shared (readonly)
*/

static int inline cubefree(uint32_t k)
{
    uint64_t p,q;
    for ( int i = 1 ; ; i++ ) {
        p = _primes_small_primes[i]; 
        if ( (q=p*p*p) > k ) return 1;
        if ( !(k%q) ) return 0;
    }
}

#define MAXK        1000        // Must exceed 2^16/27
#define K27MAXN     388         // Maximum number of admissible z's mod 27*k for any d mod 27*k for k < 1000 with 3-adic valuation 1

static inline int goodk(uint32_t k) { return k && k <= MAXK && !mod3(k) && mod9(k) && cubefree(k); }

// To measure the benefit of lifting arithmetic progressions of z (for a fixed d) viewed as a subset S of Z/rZ to Z/rmZ for some m coprime to r
// we use the "benefit" function below which returns a 32-bit approximation to 2^30 * 1-log(n)/log(m), where n is the number of admissible z's mod m
// the rational number benefit(n,m)/2^30 approximates the number of "bits per bit" we gain by lifing S mod r to S mod rm
// 0 bits per bit means the projection Z/rmZ -> Z/mZ has maximal fibers above every z in S mod r (so #(S mod rm) = m * #(S mod r))
// 1 bits per bit means the projection Z/rmZ -> Z/mZ restricts to an injection S mod rm -> S mod m (so #(S mod rm) = #(S mod r))
static inline uint32_t benefit(int n, int m) { softassert(n>0 && n <= m); return floor((1<<30)*(1.0-log(n)/log(m))); }

static uint16_t K;              // global shared value of k stored in 16 bits (we don't use k because this is often a local variable/counter)
static uint16_t kpcnt;          // number of primes other then 3 dividing k (could be 0)
static uint16_t kp[4];          // list of primes that divide k
static uint8_t kv[4];           // kv[i] is the valuation of k at the prime kp[i]
static uint16_t kq[4];          // kp[i]^kv[i]
static int keps;                // 1 for k=3 mod 9, -1 for k=6 mod 9

static inline unsigned sgnz_index (uint64_t d) { return (unsigned)(1+keps*ui64_kronecker3(d))>>1; }    // sgnz index (0=-1, 1=1)

static uint16_t k27;            // 27k
static uint16_t k27m;           // Divisor of 27k throught which cubic reciprocity constraints factor; not currently used
static uint64_t k27minv;        // floor(2^64/(27k)) // switch to floor(2^64/m)) when k27m is used
static uint16_t *k27zs;         // dynamicall allocated buffer into which entries in k27tab point and k27ftab[i]->ztab point
static uint16_t *k27itab;       // table of inverses of d mod 27k indexed by d mod 27k (followed by tables for k27ftab[i]->itab)
static uint16_t *k27zcnts;      // table of counts of admissible z's mod 27k, indexed by d mod 27k (followed by tables for k27ftab[i]->zcnts)
static uint32_t *k27ztab;       // table of offests into k27zs, indexed by d mod 27k (followed by tables for k27ftab[i]->ztab)

static uint64_t kdmax[9];       // use d <= dbmax[i] to test d*kd[i] <= dmax, zero terminated, at most 8 nonzero entries
static uint16_t kdmin;          // smallest admissible d|k greater than 1 (0 if none)
static uint16_t kdcnt;          // number of admissible d|k
static struct kdrec {           // table with records for each admissible d|k
    uint16_t d;                 // admissible d | k (so d is prime to 3 and v_p(d) = v_p(k) for all p|d (note k is cubefree)
    uint8_t n;                  // number of cuberoots of k mod d (just 1 if d is squarefree, since then 0 is the only cuberoot)
    uint8_t fi;                 // index into k27ftab of m = lcm(9*d,2) -- we will always lift at least to this m (which will have zcnts[d] == n)
    uint32_t fmask;             // bitmask whose ith bit is set if k27ftab[i].m is properly divisible by d and beneficial
} kdtab[8];                     // for k <= 1000 at most 7 nontrivial admissible d | k, we use entry 0 for 1 (meaning d is coprime to k)

#define MAXK27FCNT  24          // maximum number of divisors m of 27k divisible by gcd(18,3k) for k < 1000
static uint16_t k27fcnt;        // actual number of divisors m of 27k divisible by gcd(18,3k) for our k
static struct k27frec {         // table of these divisors m
    uint16_t m;                 // gcd(3k,18) | m | 27k
    uint16_t unused;
    uint32_t ztot;              // total number of zs stored in k27zs for m (at most 2*m*m/3, but usually a lot less)
    uint64_t minv[4];           // floor(2^64/m), floor(2^64/(2m)), floor(2^64/(7m)), floor(2^64/(14m)) precomputed for Barrett reduction
    uint16_t *itab;             // table of inverses of d mod m indexed by d mod m
    uint16_t *zcnts;            // zcnts[d] is length of ztab[d] for d mod m
    uint32_t *ztab;             // table of offsets into k27zs, indexed by d mod m
} k27ftab[MAXK27FCNT];

static inline uint32_t crt2 (uint64_t za, uint64_t a, uint32_t z2) { return za + a*(z2^(za&1)); }
static uint8_t _inv7[7] = {0,1,4,5,2,3,6};
static inline uint32_t inv7 (uint64_t a) { return _inv7[mod7(a)]; }
static inline uint32_t crt7 (uint64_t za, uint64_t a, uint32_t z7) { return za + a*mod7((z7+7-mod7(za))*inv7(a)); }
static inline uint32_t crt14 (uint64_t za, uint64_t a, uint32_t z14) { return crt2(crt7(za,a,mod7(z14)),7*a,z14&1); }

// km1,km2,km7,km14 are all divisible by gcd(3k,18) (and by 81 for k=3) and have a unique z per d
// these are the moduli we will use when d is coprime to k (this includes all prime d since we never allow d|k)
static uint32_t km1,km2,km7,km14,kmzs[243],kminvs[243]; // 243 is max(81+162,9+18+63+126)
static uint32_t *km1ztab,*km2ztab,*km7ztab,*km14ztab;   // pointers into kmztab
static uint32_t *km1itab,*km2itab,*km7itab,*km14itab;   // pointers into kmitab
static uint32_t km[4], *kmztab[4], *kmitab[4];          // km[] = {km1,km2,km7,km14}, ...
static uint64_t *kminv;


#define MAXK27BCNT 58           // for admissible k < 1000 (of these at most 45 come from beneficial m)
static uint16_t k27bcnt;        // number of distinct benefit(w,m) values
static struct k27brec {
    uint16_t fi;                // index of divisor of 27k listed in k27ftab
    uint16_t w;                 // number of residue classes mod m
    uint32_t b;                 // benfit(w,m)
    uint32_t fmask;             // bitmap with ith bit set, for the unique i for which k27ftab[i].m == m
} k27btab[MAXK27BCNT];

static uint8_t *k27rtab;        // list of k27fcnt-element vectors of indexes into 27btab, entry d*k27fcnt holds the entry for d mod k27

static int ui16_cmp (const void *a, const void *b)
    { return *((uint16_t*)a) < *((uint16_t*)b) ? -1 : ( *((int16_t*)a) > *((int16_t*)b) ? 1 : 0 ); }
static int ui32_cmp (const void *a, const void *b)
    { return *((uint32_t*)a) < *((uint32_t*)b) ? -1 : ( *((int32_t*)a) > *((int32_t*)b) ? 1 : 0 ); }
//static int ui64_cmp (const void *a, const void *b)
//  { return *((uint64_t*)a) < *((uint64_t*)b) ? -1 : ( *((int64_t*)a) > *((int64_t*)b) ? 1 : 0 ); }

static inline uint16_t k27red (uint64_t a)
    { return b32_red (a,k27,k27minv); }

// returns a list of indexes into k27ftab of divisors compatible with ki (properly divisible by kdtab[ki]) ranked by benefit
// such that each divisor is larger than the previous and brings additional benefit relative to the previous one
static inline unsigned ranked_mi (uint8_t mis[MAXK27FCNT], uint32_t bs[MAXK27FCNT], uint64_t d, uint16_t ki)    // ki is an index into kdtab
{
    if ( K == 3 ) return 0;
    struct k27brec *x;
    uint8_t *r = k27rtab + k27red(d)*k27fcnt;
    uint32_t m, mm, w;
    unsigned i, n;

    softassert (ki < kdcnt);
    uint32_t fmask = kdtab[ki].fmask;
    softassert (fmask);
    // get our first choice (in terms of benefit/bit)
    for ( i = 0 ; i < k27fcnt ; i++ ) { x = k27btab+r[i]; if ( fmask & x->fmask ) { mis[0] = x->fi; bs[0] = x->b; w = x->w; m = k27ftab[mis[0]].m; break; } }
    softassert ( i < k27fcnt );
    // add successively worse divisors as long as they are larger than the previous and offer some relative benefit
    for ( n = 1 ; i < k27fcnt ; i++ )
        { x = k27btab+r[i]; if ( fmask & x->fmask && (mm=k27ftab[x->fi].m) > m && w*mm > m*x->w ) { mis[n] = x->fi; bs[n++] = x->b; w = x->w; m = mm; } }
    return n;
}

// sets d[] to a sorted list of divisors of 16-bit integer with prime factorization prod_{1<=i<=n} p[i]^e[i], returns length = number of divisiors
static inline int ui16_divisors (uint16_t d[], uint16_t p[], int e[], int n)
{
    int v[n];
    int i, j, k, s;

    assert (n);
    memset(v,0,sizeof(v));
    for ( s = 0 ; v[0] <= e[0] ; s++ ) {
        for ( i = 0, k = 1 ; i < n ; i++ ) for ( j = 0 ; j < v[i] ; j++ ) k *= p[i];
        assert (!s||k != d[s-1]);
        d[s] = k;
        v[n-1]++;
        for ( i = n-1 ; i && v[i] > e[i] ; i-- ) { v[i] = 0; v[i-1]++; }
    }
    qsort (d, s, sizeof(d[0]), ui16_cmp);
    return s;
}

void precompute_kdata (uint32_t k, uint64_t dmax)
{
    uint64_t *bm, bytes, mem=0;
    uint32_t *ztab, *w32, z;
    uint16_t *invs, *cnts, *zs, *w16;
    uint64_t p, minv;
    int i, ii, j, d, dd, m, mm, n, max, tot, totzs;
    int sk27;

    assert (goodk(k));

    report_timer_reset();

    // compute the prime factorization of k (at most 4 prime factors)
    for ( i = 1 ; (p=_primes_small_primes[i]) <= k ; i++ ) {
        if ( k%p ) continue;
        j = ( k > p*p && k%(p*p) == 0 ) ? 2 : 1;
        if ( p == 3 ) assert ( j == 1 );
        assert ( k < p*p*p || k%(p*p*p) );  // k must be cubefree
        assert ( kpcnt < 4 );
        kp[kpcnt] = p; kv[kpcnt] = j; kq[kpcnt] = j == 1 ? p : p*p;
        kpcnt++;
    }
    K = k;
    keps = ( mod9(k)==3 ? 1 : -1 );
    k27 = 27*k;  k27minv = b32_inv(k27);

    // compute list of divisors of 27*k
    uint16_t k27factors[64];
    int k27e[kpcnt];
    for ( i = 0 ; i < kpcnt ; i++ ) k27e[i] = (kp[i] == 3) ? 4 : kv[i];
    k27fcnt = ui16_divisors(k27factors, kp, k27e, kpcnt);
    assert (k27fcnt*sizeof(k27factors[0]) < sizeof(k27factors) && k27factors[0] == 1 && k27factors[k27fcnt-1] == k27);

    // remove divisors not divisible by mmin = k==3 ? 81 : gcd(18,3k), we will always use m divisible by mmin, since the benefit for mmin is 1 bit/bit
    mm = (k==3 ? 81 : 9*(k&1?1:2));
    for ( i = j = 0 ; i < k27fcnt ; i++ ) if ( !(k27factors[i]%mm) ) k27factors[j++] = k27factors[i];
    k27fcnt = j;
    assert (k27fcnt && k27fcnt*sizeof(k27ftab[0]) <= sizeof(k27ftab));

    for ( i = 0, sk27 = 0 ; i < k27fcnt ; i++ ) sk27 += k27factors[i];

    // precompute table of inverses mod 27*k and factors thereof
    k27itab = invs = shared_calloc (bytes=sk27*sizeof(*k27itab));  mem += bytes;
    k27zcnts = cnts = shared_calloc (bytes=sk27*sizeof(*k27zcnts));  mem += bytes;
    k27ztab = ztab = shared_calloc (bytes=sk27*sizeof(*k27ztab));  mem += bytes;
    w16 = malloc(2*k27*sizeof(*w16));   // workspace for calls to invtab16
    int k7 = mod7(k*k) == 4;    // if k is +/-2 mod 7 we will want to lift mod 7m for 3/7 of the d
    for ( i = k27fcnt-1 ; i >= 0 ; i-- ) {
        k27ftab[i].m = m = k27factors[i];
        k27ftab[i].minv[0] = minv = b32_inv(k27ftab[i].m);
        k27ftab[i].minv[1] = (m&1) ? b32_inv(2*k27ftab[i].m) : 0;
        k27ftab[i].minv[2] = k7 ? b32_inv(7*k27ftab[i].m) : 0;
        k27ftab[i].minv[3] = (m&1) && k7 ? b32_inv(14*k27ftab[i].m) : 0;
        k27ftab[i].itab = invs;
        k27ftab[i].zcnts = cnts;
        k27ftab[i].ztab = ztab;
        if ( m == k27 ) assert (invs == k27itab);
        invtab16 (invs, m, kp, kpcnt, w16);
        invs += m; cnts += m; ztab += m;
    }
    assert (k27ftab[0].m == mm);
    free (w16);

    // compute admissible z's mod 27k (replaces load_kfile)
    n = admissible (&k27zs, &k27m, k27ztab, k27zcnts, k);

    // we now want to reduce admissible zs and ds mod all proper divisors m of 27k
    // first figure out how much space we are going to need
    bm = bm_alloc (k27);
    totzs = 1;  // skip first entry (zero offset is reserved for null
    for ( i = k27fcnt-1 ; i >= 0 ; i-- ) {
        m = k27ftab[i].m; minv = k27ftab[i].minv[0];
        cnts = k27ftab[i].zcnts;
        tot = 0; max = 0;
        for ( d = 1 ; d < m ; d++ ) { // d is prime to 3 hence not 0 mod m (which is divisible by 9)
            if ( !(d%3) ) continue;
            if ( m < k27 ) {
                bm_erase (bm,m);
                // mark residue classes mod m of admissible z mod k27 for all lifts of d mod k27
                for ( dd = d ; dd < k27 ; dd += m ) for ( j = 0 ; j < k27zcnts[dd] ; j++ ) bm_set(bm,b32_red(k27zs[k27ztab[dd]+j],m,minv));
                cnts[d] = bm_weight(bm,m);
            }
            if ( !cnts[d] ) continue;
            tot += cnts[d];  if ( cnts[d] > max ) max = cnts[d];
            // add (m,w) to benefit table if it is new (this is a linear search of a list of at most 50 elements)
            for ( j = 0 ; j < k27bcnt ; j++ ) if ( k27btab[j].fi == i && k27btab[j].w == cnts[d] ) break;
            if ( j == k27bcnt ) {
                assert (sizeof(k27btab[0])*k27bcnt < sizeof(k27btab));
                k27btab[j].fi = i; k27btab[j].w = cnts[d]; k27btab[j].b = m == mm ? (1<<30) : benefit (cnts[d],m/mm); k27btab[j].fmask = (uint32_t)1 << i;
                k27bcnt++;
            }
        }
        k27ftab[i].ztot = tot;
        if ( i == k27fcnt-1 ) assert (tot == n);
        totzs += tot;
        //if ( m > mm ) report_printf ("27k-divisor m=%u has an average of %.2f z's per admissible d, max %d, worstcase relative benefit is %.3f bits/bit\n", m, (double)tot/(2*m/3), max, 1.0-log(max)/log(m/mm));
    }

    // extend k27zs and put it in shared memory
    void *ptr = shared_malloc (bytes=totzs*sizeof(*k27zs));  mem += bytes;
    memcpy (ptr, k27zs, k27ftab[k27fcnt-1].ztot*sizeof(*k27zs)); free (k27zs); k27zs = ptr;

    zs = k27zs + 1 + k27ftab[k27fcnt-1].ztot;
    for ( i = k27fcnt-2 ; i >= 0 ; i-- ) {
        m = k27ftab[i].m; minv = k27ftab[i].minv[0];
        cnts = k27ftab[i].zcnts;
        ztab = k27ftab[i].ztab;
        for ( d = 1 ; d < m ; d++ ) { // d is prime to 3 hence not 0 mod m (which is divisible by 9)
            if ( !cnts[d] ) continue;
            ztab[d] = zs-k27zs;
            bm_erase (bm,m);
            // mark residue classes mod m of admissibles z mod k27 for all lifts of d mod k27
            for ( dd = d ; dd < k27 ; dd += m ) for ( j = 0 ; j < k27zcnts[dd] ; j++ ) bm_set(bm, b32_red(k27zs[k27ztab[dd]+j],m,minv));
            for ( ii = 0, j = bm_next_set(bm,0,m) ; j < m && ii < cnts[d] ; j = bm_next_set(bm,j+1,m), ii++ ) *zs++ = j;
            assert (j >= m && ii == cnts[d]);
            assert (zs-k27zs <= totzs);
        }
    }
    bm_free (bm);
    assert (zs-k27zs == totzs);

    // Set up km1,km2,km7,km14 -- these are multiples of mm=9,18,81 that have only one z per d
    // if k is even only km1,km7 are relevant, and k7,k14 are relevant only for k=+/-2 mod 7
    // We will always lift modulo a multiple of the largest of these we can for a given d, and for large d we won't consider anything else.
    km1 = k27ftab[0].m; if ( km1&1 ) km2 = 2*km1;
    if ( mod7(k*k) == 4 ) { km7 = 7*km1; km14 = 7*km2; };
    km1itab = kminvs; w32 = km1itab+km1; km1ztab = kmzs; ztab = km1ztab+km1;
    if ( km2 ) { km2itab = w32; w32 += km2; km2ztab = ztab; ztab += km2; }
    if ( km7 ) { km7itab = w32; w32 += km7; km7ztab = ztab; ztab += km7; }
    if ( km14 ) { km14itab = w32; km14ztab = ztab; }
    w32 = malloc(2*_max(_max(km1,km2),_max(km7,km14))*sizeof(*w32));    // workspace for calls to invtab32
    uint32_t kp1[kpcnt];  for ( i = 0 ; i < kpcnt ; i++ ) kp1[i] = kp[i];
    invtab32 (km1itab, km1, kp1, kpcnt, w32);
    cnts = k27ftab[0].zcnts;  ztab = k27ftab[0].ztab;
    for ( d = 1 ; d < km1 ; d++ ) if ( cnts[d] ) { assert (cnts[d]==1); km1ztab[d] = k27zs[ztab[d]]; }
    if ( km2 ) {
        uint32_t kp2[kpcnt+1]; kp2[0] = 2; for ( i = 0 ; i < kpcnt ; i++ ) kp2[i+1] = kp[i];
        invtab32 (km2itab, km2, kp2, kpcnt+1, w32);
        // z=0 mod 2 only depends on d mod km1 (and both d and km1 are odd if we are in this case, but set both 
        for ( d = 1 ; d < km1 ; d++ ) if ( cnts[d] ) { z = crt2(k27zs[ztab[d]],km1,0); km2ztab[d] = km2ztab[d+km1] = z; }
    }
    if ( km7 ) {
        uint32_t kp7[kpcnt+1]; for ( i = 0 ; i < kpcnt && kp[i] < 7 ; i++ ) { kp7[i] = kp[i]; } for ( kp7[i] = 7; i < kpcnt ; i++ ) kp7[i+1] = kp[i];
        invtab32 (km7itab, km7, kp7, kpcnt+1, w32);
        // z=0 mod 7 only depends on d mod km1 (this will only happen for suitable d, those for which onezmod7(d,si) returns true), here we assume this holds)
        for ( d = 1 ; d < km1 ; d++ ) if ( cnts[d] ) { z = crt7(k27zs[ztab[d]],km1,0); for ( i = 0 ; i < 7 ; i++ ) km7ztab[d+km1*i] = z; }
    }
    if ( km14 ) {
        uint32_t kp14[kpcnt+2]; kp14[0] = 2; for ( i = 0 ; i < kpcnt && kp[i] < 7; i++ ) { kp14[i+1] = kp[i]; } for ( kp14[i+1] = 7; i < kpcnt ; i++ ) kp14[i+2] = kp[i];
        invtab32 (km14itab, km14, kp14, kpcnt+2, w32);
        // z=0 mod 14 only depends on d mod km1 (this will only happen for suitable d, those for which onezmod7(d,si) returns true), here we assume this holds)
        for ( d = 1 ; d < km1 ; d++ ) if ( cnts[d] ) { z = crt14(k27zs[ztab[d]],km1,0); for ( i = 0 ; i < 14 ; i++ ) km14ztab[d+km1*i] = z; }
    }
    free (w32);
    km[0] = km1; km[1] = km2; km[2] = km7; km[3] = km14;
    verbose_printf ("km=[%u,%u,%u,%u]\n",km1,km2,km7,km14);
    kmitab[0] = km1itab; kmitab[1] = km2itab; kmitab[2] = km7itab; kmitab[3] = km14itab; 
    kmztab[0] = km1ztab; kmztab[1] = km2ztab; kmztab[2] = km7ztab; kmztab[3] = km14ztab; 
    kminv = k27ftab[0].minv;

    // rank k27 divisors for each d mod 27k according to benefit
    k27rtab = shared_calloc (bytes=sk27*k27fcnt*sizeof(*k27rtab));  mem += bytes;
    for ( d = 1 ; d < k27 ; d++ ) {
        if ( !k27zcnts[d] ) continue;
        uint8_t *r = k27rtab+d*k27fcnt;
        for ( i = 0 ; i < k27fcnt ; i++ ) {
            m = k27ftab[i].m; minv = k27ftab[i].minv[0];
            ii = k27ftab[i].zcnts[b32_red(d,m,minv)];
            for ( j = 0 ; j < k27bcnt ; j++ ) if ( k27btab[j].fi == i && k27btab[j].w == ii ) break;
            assert ( j < k27bcnt );
            r[i] = j;
        }
        // sort r in decreasing order by k27btab[r[i]].b
        for ( i = 1 ; i < k27fcnt ; i++ ) { ii = r[i]; for ( j = i-1; j >= 0 && k27btab[r[j]].b < k27btab[ii].b ; j--) { r[j+1] = r[j]; } r[j+1] = ii; }
    }

    // We now remove 3 from list of prime factors of k, since it cannot divide any admissible d
    for ( i = j = 0 ; i < kpcnt ; i++ ) if ( kp[i] != 3 ) { kp[j] = kp[i]; kv[j] = kv[i]; kq[j] = kq[i]; j++; }
    kpcnt = j;

    // Because k is cubefree, any admissible d must satisfy v_p(d) = v_p(k) for all primes p|d
    kdcnt = (1<<kpcnt);
    kdmin = 0;
    for ( i = 0 ; i < kdcnt ; i++ ) {
        m = n = 1;  // compute d = m*n*n with m and n squarefree and coprime, for k <= 1000 we have n <= 31
        for ( int j = 0 ; j < kpcnt ; j++ ) if ( i&(1<<j) ) { if ( kv[j] == 2 ) n *= kp[j]; else m *= kp[j]; }
        kdtab[i].d = m*n*n;
        kdtab[i].n = n;
        // now lookup m=lcm(d,mm) in k27ftab to get fi, and compute fmask identifying divisors of 27k we might want to lift to for this d
        m = ui64_lcm(kdtab[i].d,mm);
        kdtab[i].fmask = 0;
        kdtab[i].fi = k27fcnt;  // sanity check
        for ( j = 0 ; j < k27fcnt ; j++ ) {
            if ( k27ftab[j].m == m ) kdtab[i].fi = j;
            else if ( !(k27ftab[j].m % m) ) {
                n = k27ftab[j].m / m;
                if ( n%4 && n%49 && n%169 ) kdtab[i].fmask |= 1<<j; // relative factors of 2^2, 7^2, 13^2 bring 0 benefit, so skip these
            }
        }
        assert (kdtab[i].fi < k27fcnt);
        if ( kdtab[i].d > 1 ) if ( ! kdmin || kdtab[i].d < kdmin ) kdmin = kdtab[i].d;
    }
    qsort (kdtab, kdcnt, sizeof(kdtab[0]), ui16_cmp);
    for ( int i = 0 ; i < kdcnt ; i++ ) kdmax[i] = dmax / kdtab[i].d;
    report_printf ("Precomputed %u (d,z) pairs via cubic reciprocity mod divisors of 27*k=%d in %.1fs using %.1f MB shared memory\n",
                    totzs, k27, report_timer_elapsed(), (double) mem/(1<<20));
}
