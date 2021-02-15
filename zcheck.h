#include "b32.h"
#include "m64.h"
#include "cstd.h"

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

/*
    This module precomputes admissible z modulo small primes (and products of small primes) that are used both for splitting/lifting arithmetic progressions 
    into a multiple shorter progressions (modulo a larger modulus), and for testing candidate values of z modulo auxilliary moduli coprime to d, and uses
    this precomputed data to support functions for testing z's in specified lists of arithmetic progressions.

    We support progressions modulo m < 2^94 using a CRT representation of m=a*b with a < 2^63 and b < 2^31.  Typically a will be divisible by the part of
    d coprime to k and b will be divisible by gcd(d,k) and any power of 3 we are lifting to (e.g. 9 or 81).  The functions below take d,a,b as separate inputs.

    The main interfaces are

        * zrcheckone -- used to check z's in a list of arithmetic progressions of length one (so moduluo m=a*b > zmax)
        * zrcheckafew -- used to check z's in a shortish (< ZFEW) list of short arithmetic progressions (so modulo m=a*b > zmax/ZSHORT)
        * zrchecmany -- used to check many z's (either a few long progressions or many short ones), this will compute bitmaps for ztesting
                        that are customized to the pair (k,d) we are considering (it assumes there are enough z's to check to make this worth doing)
        * zrchecklift -- used to lift/split long progressions in to multiple shorter ones (critical when zmax/d is large) and then apply zrcheckmany

    All the data in this file is intended to be shared/readonly except for 6 thread/child local buffers (two bitmaps and two pairs of lists of z's mod a,b)
*/

#define DMAX        ((1UL<<63)-1)
#define ZMAXBITS    95
#define ZMAX        (((uint128_t)1<<ZMAXBITS)-1)

#define ZSHORT      48      // we only call zrchecklift/many (which increases the number of progressions and shortens them) for progressions longer than this
                            // (after lifting mod the largest of km1,km2,km3,km4 we can use, this is done before ZSHORT is tested)
#define ZFEW        512     // we only call zrchecklift/many when we have least this many z's to check
#define ZBUFBITS    24      // we allocate 2 zabufs and 2 zbbufs to hold 1<<ZRBUFBITS entries each, permitting up to 1<<(2*ZRMAXBITS) z-progressions for a given d
                            // memory utilization is 24*(1<<ZRBUFBITS) bytes (per core)
                            // lowering ZRBUFBITS will reduce the extent to which we can split progressions (the code will work just more slowly)
#define BMBITS      21      // allow bitmap with 128*128*128 entries

// Thread local buffers
static uint64_t *zabuf[2];  // each zabuf points to a thread-private buffer with (1<<ZRBUFBITS) entries
static uint32_t *zbbuf[2];  // ditto
static uint64_t *bm0buf;    // thread-private buffer of size (1<<BMBITS)/8 bytes used for computing custom bitmaps
static uint64_t *bm1buf;    // digtto

// Everything from hear down is precomputed and then shared
#define PI64        16
#define SUMP64      496
static uint32_t p64[PI64+1] = {5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,0}; // divisors of k will be removed from this list
static uint64_t p64inv[PI64];       // p64inv[i] = b32_inv(p64[i])
static uint32_t *p64itab[PI64];     // p64itabs[i] points to a list of inverses modulo p64[i] (stored in p128ibuf)
static uint8_t p64pitab[64];        // p64pitab[p] holds the index of p in p64 or 0xFF if not present
static unsigned p64cnt = PI64;      // decremented to remove divisors of k at startup
static uint64_t p64sqmask[PI64];    // bit mask whose jth bit is set of j is a squre mod p64[i]

static inline uint16_t p64pimask(uint64_t p) { return ( p < 64 && p64pitab[p] >= 0 ? (uint16_t)1 << p64pitab[p] : 0 ); }
static inline unsigned sqmodp64 (int n, int pi) { return (p64sqmask[pi] & ((uint64_t)1 << n)) ? 1 : 0; }

#define PI128       29
#define SUMP128     1715
static uint32_t p128[PI128+1] = {5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,0}; // divisors of k will be removed
static uint64_t p128inv[PI128];
static uint32_t *p128itab[PI128];   // p128itabs[i] points to a list of inverses modulo p128[i] (stored in p128ibuf)
static uint8_t p128pitab[128];      // unused entries marked with 0xFF
static unsigned p128cnt = PI128;    // decremented to remove divisors of k at startup
static uint128_t p128sqmask[PI128]; // bit mask whose jth bit is set of j is a square mod p128[i]
static uint32_t p128ibuf[SUMP128];  // buffer to hold inverses mod p

static inline uint16_t p128pimask(uint64_t p) { return ( p < 128 && p128pitab[p] >= 0 ? (uint16_t)1<<p128pitab[p] : 0 ); }
static inline unsigned sqmodp128 (uint32_t n, unsigned pi) { softassert(pi<p128cnt && n < p128[pi]); return (p128sqmask[pi] & ((uint128_t)1 << n)) ? 1 : 0; }

static inline void precompute_smallp (int k)
{
    uint128_t m128;
    uint64_t pinv;
    uint32_t r,p,*invs;
    unsigned i,j;

    assert ( k > 0 && k <= MAXK && !(k%3) && (k%9) );

    // precompute data for the primes p in [5,127] not dividing k
    invs = p128ibuf;
    for ( i = j = 0 ; i < PI128 ; i++ ) {
        p = p128[i];
        if ( (k%p) ) {
            p128[j] = p128[i];
            p128inv[j] = pinv = b32_inv(p);
            for ( r = 2, m128 = 3 ; r <= p/2 ; r++ ) m128 |= ((uint128_t)1) << b32_red(r*r,p,pinv);
            p128sqmask[j] = m128;
            p128itab[j] = invs; *invs++ = 0; *invs++ = 1;
            for ( r = 2 ; r < p ; r++ ) *invs++ = ui32_inverse(r,p);    // we don't care about speed here
            j++;
        }
    }
    p128[p128cnt=j] = 0;
    for ( i = 0 ; i < p128cnt && p128[i] < 64 ; i++ )
        { p64[i] = p128[i]; p64inv[i] = p128inv[i]; p64sqmask[i] = (uint64_t)p128sqmask[i]; p64itab[i] = p128itab[i]; }
    p64[p64cnt=i] = 0;

    for ( i = 0 ; i < 64 ; i++ ) p64pitab[i] = 0xFF;
    for ( i = 0 ; i < p64cnt ; i++ ) p64pitab[p64[i]] = i;
    for ( i = 0 ; i < 128 ; i++ ) p128pitab[i] = 0xFF;
    for ( i = 0 ; i < p128cnt ; i++ ) p128pitab[p128[i]] = i;
}

// each pXXXzmask[(s+1)/2][d mod p] points to a list of p bit masks where the dth mask has the |z|th bit set if 3*d*(4*(|z|^3-s*k)-d^3) is a square modulo p
// here s = +/-1 and z = s*|z|; if we put x = 12*d and y = -(3*d*4*s*k+d^3) then we are checking if x*|z|^3+y is square mod p
static uint64_t *p64zmask[2][PI64];
static uint128_t *p128zmask[2][PI128];

// input d should be reduced mod p64[pi] (use b32_red(d,p64[pi],pinv64[pi]) to do this), and similarly for p128
// returns a bitmask whose zth bit is set if 3d*(4*s*(z^3-k)-d^3) is a square mod p64[pi] (resp. p128[pi])
// si := (s+1)>>1 (so si=0 for s=-1, si=1 for s=1 )
static inline uint64_t zsmodp64 (uint32_t d, unsigned si, unsigned pi)
    { softassert(si<2 && pi < p64cnt && d < p64[pi]); return p64zmask[si][pi][d]; }
static inline uint128_t zsmodp128 (uint32_t d, unsigned si, unsigned pi)
    { softassert(si<2 && pi < p128cnt && d < p128[pi]); return p128zmask[si][pi][d]; }
static inline uint64_t zsmodp64red (uint64_t d, unsigned si, unsigned pi)
    { softassert(si<2 && pi < p64cnt); d = b32_red(d,p64[pi],p64inv[pi]); return p64zmask[si][pi][d]; }
static inline uint128_t zsmodp128red (uint64_t d, unsigned si, unsigned pi)
    { softassert(si<2 && pi < p128cnt); d = b32_red(d,p128[pi],p128inv[pi]); return p128zmask[si][pi][d]; }

// spbenefits is a list of the 99 possible values of floor(2^30*(1-log(N)/log(p))) for p in [5,128], used to rank primes when splitting progressions
// here N:=N(k,d,s,p) is the number of x-coords of affine rational points on the elliptic curve y^2=3*d*(4*s*(z^3-k)-d^3) over Fp (d and k are nonzero mod p)
// log(N)/log(p) is the number of bits per bit saved by splitting on p (we gain log_2(p/N) bits using log_2(p) bits, log_2(p/N)/log_2(p) = 1-log(N)/log(p)
// use the inline function benefit in kdata.h to compute/compare with these
#define MAXPBRANK   101
static uint32_t spbenefits[MAXPBRANK+1] = {0,85059442,86203354,109831207,113253569,113889144,116577556,116745845,116835946,120705117,121076315,121778150,121868967,122438461,122469028,122736905,124787176,125473405,128716376,130586253,132453850,132851209,132896999,133046586,138187261,138387611,145350702,148380211,149469923,150553012,150893222,151901558,153072324,153937337,155392272,155434841,156555260,157136667,158345120,158627567,158973593,160282974,163137268,165518932,166475735,167241898,170063875,171076300,173223968,173463459,175111852,176799760,176888859,178101273,182402354,185364315,185493462,187435721,189560653,190941163,191315614,191840695,193448937,196813111,197453708,198184041,198696515,202373102,202484175,206806598,210216042,213858132,214261459,214515090,222792016,222805103,226986554,229878752,232092217,232985888,233167756,234063387,239815435,241029409,243648410,259142850,268476561,271418593,272484965,296759255,300651673,308792714,311028999,340799003,353767703,364131223,420344998,467533997,493409806,613839580,1073741824};
static uint8_t *spbtab[2][128]; // for primes p in [5,128) not dividing k, spbtab[p][p*((s+1)>>1)+d] ranks the benefit of splitting on p for s and d
static uint8_t spbbuf[2*SUMP128];

static inline uint8_t spbrank(uint32_t d, unsigned si, uint32_t p)
    { softassert (si<2 && d < p && ((p<64&&p64pitab[p]>=0) || (p>64&&p<128&&p128pitab[p]>=0)) ); return spbtab[si][p][d]; }

// mod64zmask[(s+1)/2][d mod 64] contains a mask whose |z|th bit is set if x=3*d*(4*(|z|^3-s*k)-d^3) is a square modulo 64
// this nontrivially prevents x = 32 mod 64 for k not divisible by 4 when d is 2 mod 4 (helps for both odd and even k)
static uint64_t mod64zmask[2][64];

static uint16_t onezmod7mask;       // the 7*(s+1)/2 + (d mod 7)th bit of l7mask is set if there is only 1 admissible z mod 7 for d and s
static inline int onezmod7 (uint64_t d, unsigned si) { softassert(si<2); return onezmod7mask & (1<<(7*si+mod7(d))); }

#define SMZMASKB    3072    // all products of p128 < SMZMASKB are precomputed, should be at least 1536

// precomputed zmasks for products of small primes used for z-testing
static uint64_t sminv[SMZMASKB];
static uint64_t *smzmasks[2][2*SMZMASKB];
static uint32_t sm0,sm1,sm2,sm3;                // precomputed products of p64 primes < SMZMASKBB
static uint64_t sm0inv,sm1inv,sm2inv,sm3inv;
static uint64_t *sm0zs[2], *sm1zs[2], *sm2zs[2], *sm3zs[2];

static inline uint64_t *zsmodm (uint32_t d, unsigned si, uint32_t m)
    { softassert (si < 2 && m && m < SMZMASKB && smzmasks[si][m] && d < m);  return smzmasks[si][m] + d*((m>>6)+1); }
static inline uint64_t *zsmodmred (uint64_t d, unsigned si, uint32_t m)
    { softassert (si < 2 && m < SMZMASKB && sminv[m]); return zsmodm (b32_red(d,m,sminv[m]),si,m); }
static inline uint64_t *zsmodm0 (uint32_t d, unsigned si) { softassert(si<2 && d<sm0); return sm0zs[si] + d*((sm0>>6)+1); }
static inline uint64_t *zsmodm0red (uint64_t d, unsigned si) { softassert(si<2); return sm0zs[si] + b32_red(d,sm0,sm0inv)*((sm0>>6)+1); }
static inline uint64_t *zsmodm1 (uint32_t d, unsigned si) { softassert(si<2 && d<sm1); return sm1zs[si] + d*((sm1>>6)+1); }
static inline uint64_t *zsmodm1red (uint64_t d, unsigned si) { softassert(si<2); return sm1zs[si] + b32_red(d,sm1,sm1inv)*((sm1>>6)+1); }
static inline uint64_t *zsmodm2 (uint32_t d, unsigned si) { softassert(si<2 && d<sm2); return sm2zs[si] + d*((sm2>>6)+1); }
static inline uint64_t *zsmodm2red (uint64_t d, unsigned si) { softassert(si<2); return sm2zs[si] + b32_red(d,sm2,sm2inv)*((sm2>>6)+1); }
static inline uint64_t *zsmodm3 (uint32_t d, unsigned si) { softassert(si<2 && d<sm3); return sm3zs[si] + d*((sm3>>6)+1); }
static inline uint64_t *zsmodm3red (uint64_t d, unsigned si) { softassert(si<2); return sm3zs[si] + b32_red(d,sm3,sm3inv)*((sm3>>6)+1); }


static void precompute_zmasks (uint32_t k)
{
    uint128_t m128, *mp128, *mm128;
    uint64_t bytes, mem=0;
    uint64_t pinv, qinv, rinv, sm, m64, *mp64, *mm64, *mp, *mm;
    uint32_t z, zbig;
    uint32_t x, y, d, p, q, r, pinvq, pqinvr, t;
    int i, j, m, n, si;

    assert (goodk(k));

    report_timer_reset();

    // precompute zmasks for p in p64
    mm64 = mp64 = shared_malloc(bytes=2*SUMP64*sizeof(*mm64));  mem += bytes;
    mm128 = mp128 = shared_malloc(bytes=2*SUMP128*sizeof(*mm128));  mem += bytes;
    for ( si = 0 ; si < 2 ; si++ ) for ( i = 0 ; i < p128cnt ; i++ ) {
        p = p128[i]; pinv = p128inv[i];
        t = b32_red((k<<2),p,pinv);     // 4*k mod p
        uint32_t s = si?1:p-1;
        p128zmask[si][i] = mp128;  if ( p < 64 ) p64zmask[si][i] = mp64;
        for ( d = 0 ; d < p ; d++ ) {
            // note that p < 2^6 so 3*p^4 fits in 32 bits, as do all the expressions below
            x = b32_red(12*d,p,pinv);                                   // x = 12*d mod p
            y = b32_neg(b32_red(3*d*(s*t+d*d*d),p,pinv),p);             // y = -(3*d*4*s*k+d^3) mod p, we will iterate values of x*z^3+y
            for ( z = 0, m128 = 0 ; z < p ; z++ ) if ( sqmodp128(b32_red(x*z*z*z+y,p,pinv),i) ) m128 |= (uint128_t)1 << z;
            softassert (!(m128>>p));
            *mp128++ = m128; softassert (zsmodp128(d,si,i) == m128);
            if ( p < 64 ) { *mp64++ = (uint64_t)m128; softassert (zsmodp64(d,si,i) == (uint64_t)m128); }
        }
    }
    assert (mp64-mm64 <= 2*SUMP64); assert (mp128-mm128 <= 2*SUMP128);

    // precompute zmask mod 64
    for ( i = 0, sm = 0 ; i < 64 ; i++ ) sm |= (uint64_t)1 << ((i*i)&0x3f);
    t = (4*k)&0x3f;
    for ( si = 0 ; si < 2 ; si++ ) for ( uint32_t s = si?1:63, d = 0 ; d < 64 ; d++ ) {
        x = (12*d)&0x3f;                                                // x = 12*d mod 64
        y = 64 - ((3*d*(s*t+d*d*d))&0x3f);  y &= 0x3f;                  // y = -(3*d*4*s*k+d^3) mod 64, we will iterate values of x*z^3+y
        for ( z = 0, m64 = 0 ; z < 64 ; z++ ) if ( (sm & ((uint64_t)1 << ((x*z*z*z+y)&0x3f))) ) m64 |= (uint64_t)1 << z;
        mod64zmask[si][d] = m64;
    }

    // setupt onezmod7mask if applicable
    if ( mod7(k*k) == 4 ) {
        for ( si = 0 ; si < 2 ; si++ ) for ( d = 0 ; d < 7 ; d++ ) if ( ui64_wt(zsmodp64 (d,si,p64pitab[7])) == 1 ) onezmod7mask |= (1<<(7*si+d));
        assert (ui64_wt(onezmod7mask)==6);
    } 

    // precompute zmasks for all composite squarefree m <= SMZMASKB that are products of primes p in (5,128) not dividing k (uses a few hundred MB)
    sm = z = zbig = 0;
    for ( i = 0 ; i < p128cnt ; i++ ) for ( j = i+1 ; j < p128cnt && (m=p128[i]*p128[j]) < SMZMASKB ; j++ ) { z++; sminv[m] = b32_inv(m); sm += m*((m>>6)+1); }
    for ( i = 0 ; i < p128cnt ; i++ ) for ( j = i+1 ; j < p128cnt && p128[i]*p128[j] < SMZMASKB ; j++ )
        for ( n = j+1 ; n < p128cnt && (m=p128[i]*p128[j]*p128[n]) < SMZMASKB ; n++ ) { z++; sminv[m] = b32_inv(m); sm += m*((m>>6)+1); }

    // fixed moduli that are products of small primes to be used for fast ztesting where we don't want to optimized for d (as in zrcheckone)
    // sm2 and sm3 should be < SMZMASKB, so along with everything else, but we will need to handle sm0 and sm1 separately
    sm0 = p64[0]*p64[3]*p64[5]; sm0inv = b32_inv(sm0);
    sm1 = p64[1]*p64[2]*p64[4]; sm1inv = b32_inv(sm1);
    sm2 = p64[6]*p64[9]; sm2inv = b32_inv(sm2); assert(sm2 < SMZMASKB); // sm2 < 1333 for all admissible k < 1000
    sm3 = p64[7]*p64[8]; sm3inv = b32_inv(sm3); assert(sm3 < SMZMASKB); // sm3 < 1517 for all admissible k < 1000
    if ( sm0 >= SMZMASKB ) { sm += sm0*((sm0>>6)+1); z++; zbig++; }
    if ( sm1 >= SMZMASKB ) { sm += sm1*((sm1>>6)+1); z++; zbig++; }

    mm = mp = shared_malloc(bytes=2*sm*sizeof(*mm));  mem += bytes;
    if ( sm0 >= SMZMASKB ) {
        i = 0; j = 3; n = 5;
        p = p64[i]; q = p64[j]; r = p64[n];
        pinvq = p128itab[j][p64[i]]; qinv = p64inv[j]; rinv = p64inv[n]; pqinvr = p64itab[n][b32_red(p*q,r,rinv)];
        for ( si = 0 ; si < 2 ; si++ ) for ( sm0zs[si] = mp, d = 0 ; d < sm0 ; d++, mp += (sm0>>6)+1 )
            { b32_crt3map64 (mp, zsmodp64red(d,si,i), p, zsmodp64red(d,si,j), q, zsmodp64red(d,si,n), r, pinvq, qinv, pqinvr, rinv); softassert (zsmodm0(d,si)==mp); }
    }
    if ( sm1 >= SMZMASKB ) {
        i = 1; j = 2; n = 4;
        p = p64[i]; q = p64[j]; r = p64[n];
        pinvq = p128itab[j][p64[i]]; qinv = p64inv[j]; rinv = p64inv[n]; pqinvr = p64itab[n][b32_red(p*q,r,rinv)];
        for ( si = 0 ; si < 2 ; si++ ) for ( sm1zs[si] = mp, d = 0 ; d < sm1 ; d++, mp += (sm1>>6)+1 )
            { b32_crt3map64 (mp, zsmodp64red(d,si,i), p, zsmodp64red(d,si,j), q, zsmodp64red(d,si,n), r, pinvq, qinv, pqinvr, rinv); softassert (zsmodm1(d,si)==mp); }
    }
    for ( si = 0 ; si < 2 ; si++ )
        for ( i = 0 ; i < p128cnt ; i++ )
            for ( j = i+1 ; j < p128cnt && (m=(p=p128[i])*(q=p128[j])) < SMZMASKB ; j++ )
                for ( pinvq = p128itab[j][p], qinv = p128inv[j], smzmasks[si][m] = mp, d = 0 ; d < m ; d++, mp += (m>>6)+1 )
                    { b32_crtmap128 (mp, zsmodp128red(d,si,i), p, zsmodp128red(d,si,j), q, pinvq, qinv); softassert (zsmodm(d,si,m)==mp); }
    // the loop below takes a while, it might be worth optimizing (e.g. by CRTing against pq bitmaps already computed)
    for ( si = 0 ; si < 2 ; si++ )
        for ( i = 0 ; i < p128cnt ; i++ )
            for ( j = i+1 ; j < p128cnt && (p=p128[i])*(q=p128[j]) < SMZMASKB ; j++ )
                for ( pinvq = p128itab[j][p], qinv = p128inv[j], n = j+1 ; n < p128cnt && (m=p*q*(r=p128[n])) < SMZMASKB ; n++ )
                    for ( smzmasks[si][m] = mp, rinv = p128inv[n], pqinvr = p128itab[n][b32_red(p*q,r,rinv)], d = 0 ; d < m ; d++, mp += (m>>6)+1 )
                        { b32_crt3map128 (mp, zsmodp128red(d,si,i), p, zsmodp128red(d,si,j), q, zsmodp128red(d,si,n), r, pinvq, qinv, pqinvr, rinv);  softassert (zsmodm(d,si,m)==mp); }
    assert (mp-mm == 2*sm);
    if ( ! sm0zs[0] ) { sm0zs[0] = smzmasks[0][sm0]; sm0zs[1] = smzmasks[1][sm0]; }
    if ( ! sm1zs[0] ) { sm1zs[0] = smzmasks[0][sm1]; sm1zs[1] = smzmasks[1][sm1]; }
    sm2zs[0] = smzmasks[0][sm2]; sm2zs[1] = smzmasks[1][sm2];
    sm3zs[0] = smzmasks[0][sm3]; sm3zs[1] = smzmasks[1][sm3];

#if SLOWVERIFY
uint128_t pm,qm,rm;
uint64_t *zm;
printf ("Verifying pq zmasks..."); fflush(stdout);
    for ( si = 0 ; si < 2 ; si++ )
        for ( i = 0 ; i < p128cnt ; i++ )
            for ( pinv = p128inv[i], j = i+1 ; j < p128cnt && (m=(p=p128[i])*(q=p128[j])) < SMZMASKB ; j++ )
                for ( qinv = p128inv[j], d = 0 ; d < m ; d++ )
                    for ( pm = zsmodp128red(d,si,i), qm = zsmodp128red(d,si,j), zm = zsmodm(d,si,m), z = 0 ; z < m ; z++ )
                        assert ( ((((uint128_t)1<<b32_red(z,p,pinv))&pm) && (((uint128_t)1<<b32_red(z,q,qinv))&qm) ? 1 : 0) == bm_test(zm,z));
printf ("verified\n");
printf ("Verifying pqr zmasks..."); fflush(stdout);
    for ( si = 0 ; si < 2 ; si++ )
        for ( i = 0 ; i < p128cnt ; i++ )
            for ( pinv = p128inv[i], j = i+1 ; j < p128cnt && (p=p128[i])*(q=p128[j]) < SMZMASKB ; j++ )
                for ( qinv = p128inv[j], n = j+1 ; n < p128cnt && (m=p*q*(r=p128[n])) < SMZMASKB ; n++ )
                    for ( rinv = p128inv[n], d = 0 ; d < m ; d++ )
                        for ( pm = zsmodp128red(d,si,i), qm = zsmodp128red(d,si,j), rm = zsmodp128red(d,si,n), zm = zsmodm(d,si,m), z = 0 ; z < m ; z++ )
                            assert ( ((((uint128_t)1<<b32_red(z,p,pinv))&pm) && (((uint128_t)1<<b32_red(z,q,qinv))&qm) && (((uint128_t)1<<b32_red(z,r,rinv))&rm) ? 1 : 0) == bm_test(zm,z));
printf ("verified\n");
printf ("verifying sm0 zmasks..."); fflush(stdout);
    i = 0; j = 3; n = 5; m = sm0;
    p = p128[i]; q = p128[j]; r = p128[n]; pinv = p128inv[i]; qinv = p128inv[j]; rinv = p128inv[n];
    for ( si = 0 ; si < 2 ; si++ ) for ( d = 0 ; d < m ; d++ )
        for ( pm = zsmodp128red(d,si,i), qm = zsmodp128red(d,si,j), rm = zsmodp128red(d,si,n), zm = zsmodm0(d,si), z = 0 ; z < m ; z++ )
            assert ( ((((uint128_t)1<<b32_red(z,p,pinv))&pm) && (((uint128_t)1<<b32_red(z,q,qinv))&qm) && (((uint128_t)1<<b32_red(z,r,rinv))&rm) ? 1 : 0) == bm_test(zm,z));
printf ("verified\n");
printf ("verifying sm1 zmasks..."); fflush(stdout);
    i = 1; j = 2; n = 4; m = sm1;
    p = p128[i]; q = p128[j]; r = p128[n]; pinv = p128inv[i]; qinv = p128inv[j]; rinv = p128inv[n];
    for ( si = 0 ; si < 2 ; si++ ) for ( d = 0 ; d < m ; d++ )
        for ( pm = zsmodp128red(d,si,i), qm = zsmodp128red(d,si,j), rm = zsmodp128red(d,si,n), zm = zsmodm1(d,si), z = 0 ; z < m ; z++ )
            assert ( ((((uint128_t)1<<b32_red(z,p,pinv))&pm) && (((uint128_t)1<<b32_red(z,q,qinv))&qm) && (((uint128_t)1<<b32_red(z,r,rinv))&rm) ? 1 : 0) == bm_test(zm,z));
printf ("verified\n");
printf ("verifying sm2 zmasks..."); fflush(stdout);
    i = 6; j = 9; m = sm2;
    p = p128[i]; q = p128[j]; pinv = p128inv[i]; qinv = p128inv[j];
    for ( si = 0 ; si < 2 ; si++ ) for ( d = 0 ; d < m ; d++ )
        for ( pm = zsmodp128red(d,si,i), qm = zsmodp128red(d,si,j), zm = zsmodm2(d,si), z = 0 ; z < m ; z++ )
            assert ( ((((uint128_t)1<<b32_red(z,p,pinv))&pm) && (((uint128_t)1<<b32_red(z,q,qinv))&qm) ? 1 : 0) == bm_test(zm,z));
printf ("verified\n");
printf ("verifying sm2 zmasks..."); fflush(stdout);
    i = 7; j = 8; m = sm3;
    p = p128[i]; q = p128[j]; pinv = p128inv[i]; qinv = p128inv[j];
    for ( si = 0 ; si < 2 ; si++ ) for ( d = 0 ; d < m ; d++ )
        for ( pm = zsmodp128red(d,si,i), qm = zsmodp128red(d,si,j), zm = zsmodm3(d,si), z = 0 ; z < m ; z++ )
            assert ( ((((uint128_t)1<<b32_red(z,p,pinv))&pm) && (((uint128_t)1<<b32_red(z,q,qinv))&qm) ? 1 : 0) == bm_test(zm,z));
printf ("verified\n");
#endif

    uint8_t *rp = spbbuf;
    // compute splitting benefits for p in p128
    for ( si = 0 ; si < 2 ; si++ ) for ( i = 0 ; i < p128cnt ; i++ ) for ( spbtab[si][p=p128[i]] = rp, d = 0 ; d < p ; d++ ) {
        uint32_t n = benefit(ui128_wt(zsmodp128(d,si,i)), p);
        for ( x = 0 ; x <= MAXPBRANK ; x++ ) if ( spbenefits[x] == n ) break;   // we could binary search but for ~100 entries linear is faster
        assert (x <= MAXPBRANK);
        *rp++ = (uint8_t)(MAXPBRANK-x); // put the best first
    }
    assert (rp-spbbuf <= sizeof(spbbuf));

    report_printf ("Precomputed %u zmasks for %u p in (5,128) prime to k, %u smooth squarefree m < %d and %u larger smooth m in %.1fs using %.1f MB\n",
                    p128cnt+z, p128cnt, z-zbig, SMZMASKB, zbig, report_timer_elapsed(), (double)mem/(1<<20));
}

static mpz_t X,Y,Z;

void precompute_zchecks (int k)
{
    mpz_init2(X,384); mpz_init2(Y,192), mpz_init2(Z,96);    // handles |z| <= 2^96 and d <= 2^64/3
    precompute_smallp (k);
    precompute_zmasks (k);
}

static inline void mpz_set_ui128 (mpz_t x, uint128_t a)
    { mpz_set_ui(x,a>>64); mpz_mul_2exp(x,x,64); mpz_add_ui(x,x,a&(~(uint64_t)0)); }


// sanity check computed solution
static inline int verify_mpz (mpz_t X, mpz_t Y, unsigned si, uint128_t absZ, uint64_t d)
{
    mpz_t w1,w2,w3,Z;
    int sts;

    mpz_init(w1); mpz_init(w2); mpz_init(w3); mpz_init(Z); mpz_add(w1,X,Y); mpz_abs(w1,w1); assert (mpz_cmp_ui(w1,d)==0);
    mpz_mul(w1,X,X); mpz_mul(w1,w1,X); mpz_mul(w2,Y,Y); mpz_mul(w2,w2,Y); mpz_set_ui128(Z,absZ); if ( !si ) mpz_neg(Z,Z);
    mpz_mul(w3,Z,Z); mpz_mul(w3,w3,Z); mpz_add(w1,w1,w2); mpz_add(w1,w1,w3);
    sts = mpz_cmp_ui(w1,K)==0;
    mpz_clear(w1); mpz_clear(w2); mpz_clear(w3);
    return sts;
}


// checks whether the integer 3*d*(4*sgnz*(z^3-k)-d^3) = 3*d*(4*(|z|^3-sgn(z)*k)-d^3) is a square or not (si=0 means sgnz=-1, si=1 means sgnz=1)
// this uses about 200 clock cycles (using mpn gives a modest improvement to maybe 150, which is not worth the trouble/risk)
static inline int zcheck_mpz (uint64_t d, unsigned si, uint128_t absz)
{
    report_zcheck (absz);
    softassert ((si==0 || si==1));

    mpz_set_ui128(X,absz); mpz_mul_ui(X,X,absz);  mpz_mul_ui(X,X,absz);     // X = |z|^3
    mpz_set_si(Y,(si?-1:1)*(int)K); mpz_add(X,X,Y); mpz_mul_2exp(X,X,2);    // X = 4*(|z|^3-sgn(z)*k)
    mpz_set_ui(Y,d);  mpz_mul_ui(Y,Y,d); mpz_mul_ui(Y,Y,d);                 // Y = d^3
    mpz_sub(X,X,Y); mpz_mul_ui(X,X,d); mpz_mul_ui(X,X,3);                   // S := X = 3*d*(4*(|z|^3-sgn(z)*k)-d^3) (this needs to be square)
    if (mpz_perfect_square_p(X)) {
        // Compute corresponding X and Y
        mpz_sqrt(X,X); mpz_div_ui(X,X,3*d); mpz_add_ui(X,X,d); mpz_fdiv_q_2exp(X,X,1);  // |X| = (sqrt(S)/(3d)+d)/2
        mpz_sub_ui(Y,X,d); if ( si ) mpz_neg(X,X); else mpz_neg(Y,Y);                   // |Y| = |X|-d, sgn(X)=-sgn(Z), sgn(Y)=sgn(Z)
        softassert(verify_mpz (X,Y,si,absz,d));
        mpz_set_ui128(Z,absz); if ( !si ) mpz_neg(Z,Z);
        output_solution (K,d,X,Y,Z);
        report_s (d,absz);
        return 1;
    }
    return 0;
}

static inline int validate_pimask (uint64_t d, uint32_t m)
    { for ( int i = 0 ; i < p64cnt ; i++ ) { if ( m & (1<<i) ) { if ( (d%p64[i]) ) return 0; } else { if ( !(d%p64[i]) ) return 0; } } return 1; }

static inline uint64_t *p128crtzmaps (uint64_t *bm, uint64_t d, unsigned si, uint32_t p, uint32_t q)
{
    softassert (si < 2 && p < 128 && q < 128);
    if ( p > q ) { uint32_t x; _swap(p,q,x); }
    int i = p128pitab[p], j = p128pitab[q];
    return b32_crtmap128 (bm, zsmodp128red(d,si,i), p, zsmodp128red(d,si,j), q, p128itab[j][p], p128inv[j]);
}

static inline uint64_t *p128crt3zmaps (uint64_t *bm,  uint64_t d, unsigned si, uint32_t p, uint32_t q, uint32_t r)
{
    softassert (si < 2 && p < 128 && q < 128 && r < 128);
    if ( p > q ) { uint32_t x; _swap(p,q,x); }
    int i = p128pitab[p], j = p128pitab[q], k = p128pitab[r];  softassert (i >= 0 && j >= 0 && k >= 0);
    uint64_t rinv = p128inv[k];
    return b32_crt3map128 (bm, zsmodp128red(d,si,i), p, zsmodp128red(d,si,j), q, zsmodp128red(d,si,k), r, p128itab[j][p], p128inv[j], p128itab[k][b32_red(p*q,r,rinv)], rinv);
}

// get m best primes p < 128 by benefit for d and si
static inline int best_pi (uint8_t pis[], uint64_t d, unsigned si, unsigned m)
{
    uint16_t p,r,z;
    uint64_t pinv;
    uint16_t x[PI128];
    unsigned i,j,n;

    // the benefit of rank r is stored in spbenefits[MAXPBRANK-r], r=MAXPBRANK means benefit 0, which we skip over
    z = MAXPBRANK<<8;
    for ( n = i = 0 ; i < p128cnt ; i++ ) {
        p = p128[i]; pinv=p128inv[i];
        r = spbrank(b32_red(d,p,pinv),si,p) << 8 | i;
        if ( r >= z ) continue;
        for ( j = n; j > 0 && x[j-1] > r ; j--) { x[j] = x[j-1]; }
        x[j] = r;
        if ( n < m ) n++; else z = x[n-1];
    }
    for ( i = 0 ; i < n ; i++ ) pis[i] = x[i]&0xFF;
    return n;
}

// rank primes p < 128 by benefit for d and si, return indexes of p and benefits
static inline int ranked_pi (uint8_t pis[PI128], uint32_t bs[PI128], uint64_t d, unsigned si)
{
    uint16_t p,r;
    uint64_t pinv;
    uint16_t x[PI128];
    unsigned i,j,n;

    // the benefit of rank r is stored in spbenefits[MAXPBRANK-r], r=MAXPBRANK means benefit 0, which we skip over
    for ( n = i = 0 ; i < p128cnt ; i++ ) { p = p128[i]; pinv=p128inv[i]; r = spbrank(b32_red(d,p,pinv),si,p); if ( r < MAXPBRANK ) x[n++] = (r<<8)|i; }
    // the insertion sort below is very fast, this list is short and likely to be almost sorted already (it typically uses just 2n cycles)
    for ( i = 1 ; i < n ; i++ ) { r = x[i]; for ( j = i; j > 0 && x[j-1] > r ; j--) { x[j] = x[j-1]; } x[j] = r; }
    for ( i = 0 ; i < n ; i++ ) { pis[i] = x[i]&0xFF; bs[i] = spbenefits[MAXPBRANK-(x[i]>>8)]; }
    return n;
}

static inline int verify_cuberoots_64 (uint64_t r[], unsigned n, uint64_t d)
    { for ( unsigned i = 0 ; i < n ; i++ ) { if ( ! verify_cuberoot (r[i], K, d) ) return 0; } return 1; }

static inline int verify_cuberoots_32 (uint32_t r[], unsigned n, uint32_t d)
    { for ( unsigned i = 0 ; i < n ; i++ ) { if ( ! verify_cuberoot (r[i], K, d) ) return 0; } return 1; }

#ifdef SLOWVERIFY
static inline int sanity_check_solution (uint64_t d, uint64_t z, uint64_t m)
{
    uint64_t n = ui64_gcd(d,m); if ( n > 1 && ! verify_cuberoot(z, K, n) ) return 0;
    uint128_t x = z; x = (x*((x*x)%m))%m + m-(K%m); x *= 4;
    if ( !sgnz_index(d) ) x = m-(x%m);
    uint128_t y = d; y = (y*((y*y)%m))%m;
    x += m-y;
    x = (3*((d*x)%m))%m;
    return i64_kronecker (x,m) >= 0;
}
#else
static inline int sanity_check_solution (uint64_t d, uint64_t z, uint64_t m) { return 1; }
#endif

static inline int sanity_check_solutions_64 (uint64_t d, uint64_t z[], unsigned n, uint64_t m)
    { for ( unsigned i = 0 ; i < n ; i++ ) { if ( ! sanity_check_solution (d, z[i], m) ) return 0; } return 1; }

static inline int sanity_check_solutions_32 (uint64_t d, uint32_t z[], unsigned n, uint32_t m)
    { for ( unsigned i = 0 ; i < n ; i++ ) { if ( ! sanity_check_solution (d, z[i], m) ) return 0; } return 1; }

// used to check z's in progressions defined by (za[i] mod a, zb[j] mod b) when the modulus a*b exceeds zmax
static inline void zrcheckone (uint64_t d, unsigned si, uint64_t a, uint64_t *za, uint32_t ca, uint32_t b, uint32_t *zb, uint32_t cb, uint32_t ainvb, uint64_t binv)
{
    uint64_t zmask64;
    uint32_t i, j;

    softassert (d <= dmax && si < 2 && a < ((uint64_t)1<<63) && b <= ((uint32_t)1<<31));
    softassert (ca && cb && b32_mul(b32_red(a,b,binv),ainvb,b,binv)==1);
    softassert ((uint128_t)a*b > zmax128);
    softassert (sanity_check_solutions_64 (d, za, ca, a));
    softassert (sanity_check_solutions_32 (d, zb, cb, b));

    if ( ! report_z (d,(uint64_t)ca*cb,1,1) ) return;

    // we compute |z| mod a*b as za + c*a, where za = |z| mod a, c = (zb-za)/a mod b with zb = |z| mod b (note: za + c*a < a*b does not need to be reduced)
    // to save time in the inner loop we will precompute -za/a mod b now (and loop over zb/a mod b in the outer loop) so we can compute c with an addition mod b
    uint32_t *zbuf = zbbuf[0], *zz = zbuf;
    for ( i = 0 ; i < ca ; i++ ) *zz++ = b32_neg(b32_red(b32_red(si?za[i]:a-za[i],b,binv)*ainvb,b,binv),b);

    zmask64 = mod64zmask[si][d&0x3f];
    uint128_t zmin128 = ((uint128_t)17742641545548602771UL*d)>>62;
    uint32_t d0 = b32_red(d,sm0,sm0inv), a0 = b32_red(a,sm0,sm0inv);

    for ( j = 0 ; j < cb ; j++ ) {
        softassert (zb[j] < b);
        uint32_t x = b32_mul(si?zb[j]:b-zb[j],ainvb,b,binv);
        for ( i = 0 ; i < ca ; i++ ) {
            softassert (za[i] < a);
            uint64_t aza = !si && za[i] ? a-za[i] : za[i];
            uint64_t c = zbuf[i]+ x; if ( c >= b ) c -= b;  // c = (azb-aza)/a mod b, so aza + c*a is the CRT lift of (|z| mod a,|z| mod b) in [0,ab)   
            uint128_t z = aza + (uint128_t)c*a;
            if ( z < zmin128 || z > zmax128 ) continue;
            if ( !(zmask64 & ((uint64_t)1 << (z&0x3f))) ) continue; // this catches about 1/8 when k is not 0 mod 4 and is very cheap
            if ( !bm_test(zsmodm0(d0,si),b32_red(aza+c*a0,sm0,sm0inv)) ) continue;
            if ( !bm_test(zsmodm1red(d,si),b32_red(aza+c*b32_red(a,sm1,sm1inv),sm1,sm1inv)) ) continue;
            report_zpass (z);
            if ( !bm_test(zsmodm2red(d,si),b32_red(aza+c*b32_red(a,sm2,sm2inv),sm2,sm2inv)) ) continue;
            if ( !bm_test(zsmodm3red(d,si),b32_red(aza+c*b32_red(a,sm3,sm3inv),sm3,sm3inv)) ) continue;
            zcheck_mpz(d,si,z);
        }
    }
}


// used to check z's in progressions defined by (za[i] mod a, zb[j] mod b) when the modulus l*a*b > zmax with l smallish (depending on ZSHORT and ZFEW)
static inline void zrcheckafew (uint64_t d, unsigned si, uint64_t a, uint64_t *za, uint32_t ca, uint32_t b, uint32_t *zb, uint32_t cb, uint32_t ainvb, uint64_t binv, uint32_t l)
{
    uint128_t ab;
    uint32_t m0, m1;
    uint64_t zmask64, m0inv, m1inv, *bm0, *bm1;
    uint32_t i, j;

    softassert (d <= dmax && si < 2 && a < ((uint64_t)1<<63) && b <= ((uint32_t)1<<31));
    softassert (ca && cb && b32_mul(b32_red(a,b,binv),ainvb,b,binv)==1);
    softassert ((uint128_t)l*a*b > zmax128);
    softassert (sanity_check_solutions_64 (d, za, ca, a));
    softassert (sanity_check_solutions_32 (d, zb, cb, b));

    if ( ! report_z (d,(uint64_t)ca*cb,l,2) ) return;

    m0 = sm0; m0inv = sm0inv; bm0 = zsmodm0red (d,si);
    m1 = sm1; m1inv = sm1inv; bm1 = zsmodm1red (d,si);

    // we compute |z| mod a*b as za + c*a, where za = |z| mod a, c = (zb-za)/a mod b with zb = |z| mod b (note: za + c*a < a*b does not need to be reduced)
    // to save time in the inner loop we will precompute -za/a mod b now (and loop over zb/a mod b in the outer loop) so we can compute c with an addition mod b
    uint32_t *zbuf = zbbuf[0], *zz = zbuf;
    for ( i = 0 ; i < ca ; i++ ) *zz++ = b32_neg(b32_red(b32_red(si?za[i]:a-za[i],b,binv)*ainvb,b,binv),b);

    zmask64 = mod64zmask[si][d&0x3f];

    ab = (uint128_t)a*b;
    uint32_t a0 = b32_red(a,m0,m0inv), ab0 = b32_red((uint64_t)a0*b,m0,m0inv), a1 = b32_red(a,m1,m1inv), ab1 = b32_red((uint64_t)a1*b,m1,m1inv);

    uint128_t zmin128 = ((uint128_t)17742641545548602771UL*d)>>62;

    for ( j = 0 ; j < cb ; j++ ) {
        softassert (zb[j] < b);
        uint32_t x = b32_mul(si?zb[j]:b-zb[j],ainvb,b,binv);
        for ( i = 0 ; i < ca ; i++ ) {
            softassert (za[i] < a);
            uint64_t aza = !si && za[i] ? a-za[i] : za[i];
            uint64_t c = zbuf[i] + x; if ( c >= b ) c -= b;     // c = (azb-aza)/a mod b, so aza + c*a is the CRT lift of (|z| mod a,|z| mod b) in [0,ab)   
            uint32_t z0 = b32_red(aza+c*a0,m0,m0inv), z1 = b32_red(aza+c*a1,m1,m1inv);
            // note that r (and c) need to be 64-bits (or need to be cast them to 64 bits when multiplying below)
            for ( uint64_t r = 0 ; r < l ; r++, z0 += ab0 ) {                   // our arithmetic progression is |z| = aza + c*a + r*ab
                if ( z0 >= m0 ) z0 -= m0;
                if ( !bm_test(bm0,z0) ) continue;
                if ( !bm_test(bm1,b32_red(z1+r*ab1,m1,m1inv)) ) continue;
                uint128_t z = aza + c*(uint128_t)a + r*ab;
                if ( !(zmask64 & ((uint64_t)1 << (z&0x3f))) ) continue;
                if ( z < zmin128 || z > zmax128 ) continue;
                report_zpass (z);
                // we could cache a2, ab2, bm2 to avoid recomputing them but this does not appear to be worth doing (typically we only get here once or twice)
                uint32_t a2 = b32_red(a,sm2,sm2inv), ab2 = b32_red((uint64_t)a2*b,sm2,sm2inv);
                if ( !bm_test(zsmodm2red(d,si),b32_red(aza+c*a2+r*ab2,sm2,sm2inv)) ) continue;
                uint32_t a3 = b32_red(a,sm3,sm3inv), ab3 = b32_red((uint64_t)a3*b,sm3,sm3inv);
                if ( !bm_test( zsmodm3red(d,si),b32_red(aza+c*a3+r*ab3,sm3,sm3inv)) ) continue;
                zcheck_mpz(d,si,z);
            }
        }
    }
}


// used to check z's in progressions defined by (za[i] mod a, zb[j] mod b) when the number of progressions and/or their length is large
// pis[] contains a list of n indexes into p128 we should use for building zmasks (typically computed by zrchecklift)
static inline void zrcheckmany (uint64_t d, unsigned si, uint64_t a, uint64_t *za, uint32_t ca, uint32_t b, uint32_t *zb, uint32_t cb, uint32_t ainvb, uint64_t binv, uint8_t pis[10], unsigned n)
{
    uint128_t ab,qm0,qm1,qm2,qm3;
    uint32_t m0, m1;
    uint64_t q, q0, q1, q2, q3, cnt;
    uint64_t l, qinv, zmask64, m0inv, m1inv, q0inv, q1inv, q2inv, q3inv;
    uint64_t *bm0, *bm1;
    uint32_t i, j;

    profile_zrcheck_start();

    softassert (d <= dmax && si < 2 && a < ((uint64_t)1<<63) && b <= ((uint32_t)1<<31));
    softassert (ca && cb && b32_mul(b32_red(a,b,binv),ainvb,b,binv)==1);
    softassert (sanity_check_solutions_64 (d, za, ca, a));
    softassert (sanity_check_solutions_32 (d, zb, cb, b));

    l = fastceilboundl(zmaxld/((long double)a*b));  // This takes less than 10 cycles (using 128-bit integer division would be 50+ cycles)
    if ( n < 10 ) { zrcheckafew (d, si, a, za, ca, b, zb, cb, ainvb, binv, l); return; }

    cnt = (uint64_t)ca*cb;
    if ( ! report_z (d,cnt,l,0) ) return;

    uint32_t ps[6];
    for ( i = 0 ; i < 6 ; i++ ) ps[i] = p128[pis[i]];
    if ( !(cnt>>20) && !(l>>20) && (cnt*l) < ps[3]*ps[4]*ps[5] ) {
        m0 = ps[0]*ps[1]*ps[2]; n = 3;
        if ( m0 >= SMZMASKB ) { m0 = ps[0]*ps[1]; n = 2; }
        if ( m0 < SMZMASKB ) { m0inv = sminv[m0];  bm0 = zsmodm(b32_red(d,m0,m0inv),si,m0); }
        else { m0inv = b32_inv(m0); bm0 = p128crtzmaps (bm0buf,d,si,ps[0],ps[1]); }
        m1 = ps[n]*ps[n+1];
        if ( m1 < SMZMASKB ) { m1inv = sminv[m1];  bm1 = zsmodm(b32_red(d,m1,m1inv),si,m1); }
        else { m1inv = b32_inv(m1);  bm1 = p128crtzmaps (bm1buf,d,si,ps[n],ps[n+1]); }
        n += 2;
    } else {
        m0 = ps[0]*ps[1]*ps[2];
        if ( m0 < SMZMASKB ) { m0inv = sminv[m0];  bm0 = zsmodm(b32_red(d,m0,m0inv),si,m0); }
        else { m0inv = b32_inv(m0);  bm0 = p128crt3zmaps (bm0buf,d,si,ps[0],ps[1],ps[2]); }
        m1 = ps[3]*ps[4]*ps[5];
        if ( m1 < SMZMASKB ) { m1inv = sminv[m1];  bm1 = zsmodm(b32_red(d,m1,m1inv),si,m1); }
        else { m1inv = b32_inv(m1);  bm1 = p128crt3zmaps (bm1buf,d,si,ps[3],ps[4],ps[5]); }
        n = 6;
    }
    i = pis[n++]; q0 = p128[i]; q0inv = p128inv[i]; qm0 = zsmodp128red(d,si,i);
    i = pis[n++]; q1 = p128[i]; q1inv = p128inv[i]; qm1 = zsmodp128red(d,si,i);
    i = pis[n++]; q2 = p128[i]; q2inv = p128inv[i]; qm2 = zsmodp128red(d,si,i);
    i = pis[n];   q3 = p128[i]; q3inv = p128inv[i]; qm3 = zsmodp128red(d,si,i);
    q = q0*q1*q2*q3; qinv = b32_inv(q);

    // we will compute |z| mod a*b as za + c*a, where za = |z| mod a, c = (zb-za)/a mod b with zb = |z| mod b (note: za + c*a < a*b does not need to be reduced)
    // to save time in the inner loop we will precompute zb/a mod b now (and loop over za/a mod b in the outer loop) so we can compute c with an addition mod b
    uint32_t *zbuf = ( zb == zbbuf[0] ? zbbuf[1] : zbbuf[0] ), *zz = zbuf;
    if ( !si ) for ( j = 0 ; j < cb ; j++ ) *zz++ = b32_mul(b-zb[j],ainvb,b,binv);
    else  for ( j = 0 ; j < cb ; j++ ) *zz++ = b32_mul(zb[j],ainvb,b,binv);
    zb = zbuf;

    zmask64 = mod64zmask[si][d&0x3f];

    ab = (uint128_t)a*b;
    uint32_t a0 = b32_red(a,m0,m0inv), ab0 = b32_red((uint64_t)a0*b,m0,m0inv), a1 = b32_red(a,m1,m1inv), ab1 = b32_red((uint64_t)a1*b,m1,m1inv);
    uint32_t aq = b32_red(a,q,qinv), abq = b32_red((uint64_t)aq*b,q,qinv);

    uint128_t zmin128 = ((uint128_t)17742641545548602771UL*d)>>62;

    profile_zrcheck_setup();

    for ( i = 0 ; i < ca ; i++ ) {
        softassert (za[i] < a);
        uint64_t aza = !si && za[i] ? a-za[i] : za[i];
        uint32_t nzab = b32_neg(b32_mul(b32_red(aza,b,binv),ainvb,b,binv),b);
        uint32_t za0 = b32_red(aza,m0,m0inv), za1 = b32_red(aza,m1,m1inv);
        for ( j = 0 ; j < cb ; j++ ) {
            softassert (zb[j] < b);
            uint64_t c = nzab + zb[j]; if ( c >= b ) c -= b;    // c = (azb-aza)/a mod b, so aza + c*a is the CRT lift of (|z| mod a,|z| mod b) in [0,ab)   
            uint32_t z0 = b32_red(za0+c*a0,m0,m0inv), z1 = b32_red(za1+c*a1,m1,m1inv);
            // note that r (and c) need to be 64-bits (or need to be cast to 64 bits when multiplying below)
            for ( uint64_t r = 0 ; r < l ; r++, z0 += ab0 ) {                   // our arithmetic progression is |z| = aza + c*a + r*ab
                if ( z0 >= m0 ) z0 -= m0;
                if ( !bm_test(bm0,z0) ) continue;
                if ( !bm_test(bm1,b32_red(z1+r*ab1,m1,m1inv)) ) continue;
                uint128_t z = aza + c*(uint128_t)a + r*ab;
                if ( !(zmask64 & ((uint64_t)1 << (z&0x3f))) ) continue; // this catches about 1/8 when k is not 0 mod 4 and is really cheap so we do it first
                if ( z < zmin128 || z > zmax128 ) continue;
                report_zpass (z);
                uint32_t zq = b32_red(aza+c*aq+r*abq,q,qinv);
                if ( !(qm0 & ((uint128_t)1 << b32_red(zq,q0,q0inv))) ) continue;
                if ( !(qm1 & ((uint128_t)1 << b32_red(zq,q1,q1inv))) ) continue;
                if ( !(qm2 & ((uint128_t)1 << b32_red(zq,q2,q2inv))) ) continue;
                if ( !(qm3 & ((uint128_t)1 << b32_red(zq,q3,q3inv))) ) continue;
                zcheck_mpz(d,si,z);
            }
        }
    }

    profile_zrcheck_end();
}


void zrchecklift (uint64_t d, unsigned si, unsigned ki, uint64_t a, uint64_t *za, uint32_t ca)
{
    uint8_t pis[PI128],mis[MAXK27FCNT],qis[PI128];
    uint32_t pbs[PI128],mbs[MAXK27FCNT];
    uint128_t q, qq;
    struct k27frec *x;
    uint64_t c, binv;
    uint32_t b, cb, *zb, ainvb;
    uint32_t m, mi, dm, pmask;
    unsigned i,j, npi,nqi,nmi;

    profile_zrlift_start();

    npi = ranked_pi (pis,pbs,d,si);
    nmi = ranked_mi (mis,mbs,d,ki);
    mi = kdtab[ki].fi;  m = k27ftab[mi].m;
    q = a;
    pmask = 0; nqi = 0;
    for ( i = 0, j = 0 ; (i < npi || j < nmi) && q*m*ZSHORT < zmax128 ; ) {
        if ( j == nmi || ( i < npi && pbs[i] > mbs[j]) ) {
            if ( ((qq=q*p128[pis[i]])*m >> (zmaxbits-2)) ) { qis[nqi++] = pis[i++]; continue; }
            pmask |= (1<<pis[i++]); q = qq;
        } else {
            if ( ((q*(dm=k27ftab[mis[j]].m)) >> (zmaxbits-2)) ) { j++; continue; }
            mi = mis[j++]; m = dm;
        }
    }
    while ( i < npi ) qis[nqi++] = pis[i++];

    x = k27ftab + mi;
    b = m; binv = x->minv[0];
    dm = b32_red(d,b,binv);  softassert (mod3(dm) && (x->ztab[dm]||(m==k27&&dm==1)));
    cb = x->zcnts[dm];
    zb = zbbuf[0];
    uint16_t *r = k27zs + x->ztab[dm];
    for ( i = 0 ; i < cb ; i++ ) zb[i] = r[i]; 
    ainvb = x->itab[b32_red(a,b,binv)]; softassert(b32_red(ainvb*b32_red(a,b,binv),b,binv));
    if ( b&1 && q&1 ) {
        for ( i = 0 ; i < cb ; i++ ) if ( zb[i]&1 ) zb[i] += b; // lift to z = 0 mod 2
        if ( !(ainvb&1) ) ainvb += b;
        b *= 2;  binv = x->minv[1];
        softassert (b32_red(ainvb*b32_red(a,b,binv),b,binv)==1);
    }
    // decide whether to split a or b
    for ( unsigned pi = 0 ; pmask ; pi++, pmask >>= 1 ) {
        if ( ! (pmask&1) ) continue;
        uint32_t p = p128[pi];
        uint64_t pinv = p128inv[pi];
        c = (uint64_t)p*b;
        uint32_t *itab = p128itab[pi];
        int t = (a>>57) ? 1 : (c>>31 ? -1 : ca-cb); // for t <= 0 we split za, ow zb
        q = zsmodp128red(d,si,pi);
        uint32_t cp = ui128_wt(q), zp[cp];
        // note that bitmasks are indexed by |z|, not z, so we need to negate if s < 0
        for ( i = j = 0 ; q ; q >>= 1, i++ ) if ( (q&1) ) { softassert(i<p&&j<cp); zp[j++] = !si && i ? p-i : i; }
        // verbose_printf ("d=%lu, folding %s=%lu using p=%u with cp=%u, new ca=%u cb=%u (factor of %.3f, benefit %.3f bits/bit)\n", d, t<0?"a":"b",t<0?a:b,p,cp,ca,cb, (double)p/cp, 1.0-log((double)cp)/log(p));
        if ( t <= 0 ) {
            if ( ((uint64_t)ca*cp) >> ZBUFBITS ) { verbose_printf ("Exceeded ZRBUFBITS: d=%lu, a=%lu, ca=%u, b=%u, cb=%u, p=%u, cp=%u\n",d,a,ca,b,cb,p,cp); break; }
            uint64_t *zbuf = ( za == zabuf[0] ? zabuf[1] : zabuf[0] ), *zz = zbuf;
            uint64_t ainvp = itab[b32_red(a,p,pinv)];
            for ( i = 0 ; i < ca ; i++ ) for ( j = 0 ; j < cp ; j++ ) *zz++ = b32_crt64 (za[i],a,zp[j],p,ainvp,pinv);
            za = zbuf;  ca *= cp; a *= p;
            uint64_t pinvb = b - (((uint64_t)b*itab[b32_red(b,p,pinv)]-1) / p); // solve 1 = p*(1/p mod b) + b*(1/b mod p) for 1/p mod b, here p is small
            ainvb = b32_red(ainvb*pinvb,b,binv);
        } else {
            if ( ((uint64_t)cb*cp) >> ZBUFBITS ) { verbose_printf ("Exceeded ZRBUFBITS: d=%lu, a=%lu, ca=%u, b=%u, cb=%u, p=%u, cp=%u\n", d,a,ca,b,cb,p,cp); break; }
            uint32_t *zbuf = ( zb == zbbuf[0] ? zbbuf[1] : zbbuf[0] ), *zz = zbuf;
            uint32_t binvp = itab[b32_red(b,p,pinv)];
            for ( i = 0 ; i < cb ; i++ ) for ( j = 0 ; j < cp ; j++ ) *zz++ = b32_crt64 (zb[i],b,zp[j],p,binvp,pinv);
            ainvb = b32_crt64(ainvb,b,itab[b32_red(a,p,pinv)],p,binvp,pinv);
            zb = zbuf;  cb *= cp; b *= p; binv = b32_inv(b);
        }
        softassert(b32_mul(b32_red(a,b,binv),ainvb,b,binv)==1);
    }
    profile_zrlift_end();
    
    zrcheckmany (d, si, a, za, ca, b, zb, cb, ainvb, binv, qis, nqi);
}