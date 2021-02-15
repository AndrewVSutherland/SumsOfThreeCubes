#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

// binary gcd; assumes x and y non-zero
static uint32_t gcd(uint32_t x,uint32_t y) {
    int k,l;

    k = __builtin_ctz(x); x >>= k;
    l = __builtin_ctz(y); y >>= l;
    while (x != y)
    if (x < y)
        y -= x, y >>= __builtin_ctz(y);
    else
        x -= y, x >>= __builtin_ctz(x);
    return x<<(k<l?k:l);
}

// modular arithmetic for 0 <= x,y < m <= 2^16
static inline uint32_t modsub(uint32_t x,uint32_t y,uint32_t m) {
    uint32_t t = x-y;
    return t+(((int32_t)t>>31)&m);
}
static inline uint32_t modadd(uint32_t x,uint32_t y,uint32_t m) {
    uint32_t t = x+y-m;
    return t+(((int32_t)t>>31)&m);
}
static inline uint32_t modmul(uint32_t x,uint32_t y,uint32_t m) {
    return x*y%m; // 32-bit mul suffices since m <= 2^16
}
static uint32_t modpow(uint32_t x,uint32_t n,uint32_t m) {
    uint32_t res;
    for (res=1;n>0;n>>=1) {
        if (n & 1) res = modmul(res,x,m);
        x = modmul(x,x,m);
    }
    return res;
}

// multiplication in the field F_p[T]/(T^2+T+1) for p=2(mod 3)
// the element a+b*T (with 0 <= a,b < p) is represented as a|(b<<16)
// assumes p^2 < 2^31
static inline uint32_t ffmul(uint32_t x,uint32_t y,int32_t p) {
    int32_t x0=x&0xffff,x1=x>>16,y0=y&0xffff,y1=y>>16,z0,z1=x1*y1;
    // note that x0*y0-x1*y1 and x0*y1+x1*y0-x1*y1 are in (-p^2,p^2)
    z0 = (x0*y0-z1)%p; z0 += (z0>>31)&p;
    z1 = (x0*y1+x1*y0-z1)%p; z1 += (z1>>31)&p;
    return (z1<<16)+z0;
}

// Galois conjugate of x in F_p[T]/(T^2+T+1)
static inline uint32_t ffconj(uint32_t x,uint32_t p) {
    uint32_t x0=x&0xffff,x1=x>>16;
    x0 = modsub(x0,x1,p);
    x1 = modsub(0,x1,p);
    return (x1<<16)+x0;
}

// x^n in F_p[T]/(T^2+T+1)
static uint32_t ffpow(uint32_t x,uint32_t n,uint32_t p) {
    uint32_t res;
    for (res=1;n>0;n>>=1) {
        if (n & 1) res = ffmul(res,x,p);
        x = ffmul(x,x,p);
    }
    return res;
}

#define Z (1<<16)
#define Zbar (1+Z)
// cubic residue symbol (x/p)_3 for x in ZZ[zeta_3] and p a rational prime
// x = a+b*zeta_3 is represented as (a&0xffff)|(b<<16),
//   where a and b are signed 16-bit integers
// the result is either 0 or a cube root of 1, and is identified
//   with its image in F_2[T]/(T^2+T+1) = {0,1,Z,Zbar}
// z is a primitive cube root of 1 mod p when p=1(mod 3), precomputed for speed
static uint32_t ccmodp(int32_t x,int32_t p,int32_t z) {
    int32_t a,b,t,t1,t2;
    a = (int16_t)x % p; a += (a>>31)&p;
    b = (x>>16) % p; b += (b>>31)&p;
    if (p%3 == 2) {
        t = ffpow(a+b*Z,(p*p-1)/3,p);
        if (t <= 1 || t == Z) return t;
        return Zbar;
    }
    t = modpow((a+b*z)%p,(p-1)/3,p);
    if (!t) return 0;
    if (t == 1) t1 = 1; else if (t == z) t1 = Z; else t1 = Zbar;
    t = modpow((a+b*(p-1-z))%p,(p-1)/3,p);
    if (!t) return 0;
    if (t == 1) t2 = 1; else if (t == z) t2 = Zbar; else t2 = Z;
    return ffmul(t1,t2,2);
}

// compute table of values of chi_k(x,y) and return zmodulus(k)
// scratch must hold at least (2*k/3)^2 bytes
static uint32_t set_chi(uint8_t *chi,uint32_t k,uint32_t *scratch) {
    uint32_t f[8][3],p,np,kover3=k/3,e=kover3%3,t,r,c,i,j,x0,y0,x1,y1,m;

    // compute the prime factorization of k/3
    t = kover3, np = 0;
    for (p=2;p*p<=t;p=(p+1)|1)
        if (t % p == 0) {
            f[np][0] = p, f[np][1] = 0;
            do t /= p, f[np][1]++; while (t % p == 0);
            np++;
        }
    if (t > 1) {
        f[np][0] = t, f[np][1] = 1;
        np++;
    }

    m = 27*k;
    for (i=0;i<np;i++) {
        p = f[i][0];
        // divide m by p satisfying ord_p(k)=2 and (p=2 or 2 is not a cube mod p)
        if (f[i][1]==2 && (p==2 || (p%3==1 && modpow(2,(p-1)/3,p)!=1)))
            m /= p;

        // compute a primitive cube root of 1 for p=1(mod 3)
        if (p%3 == 1) {
            for (t=2;(uint64_t)(t*t)*t%p!=1;t++);
            f[i][2] = t;
        } else
            f[i][2] = 0;
    }

    for (x0=0;x0<kover3;x0++)
    for (y0=0;y0<=x0;y0++) {
        t = ((x0-y0)<<16) | ((-y0)&0xffff);
        for (i=0,r=1;i<np;i++) {
            c = ccmodp(t,f[i][0],f[i][2]);
            for (j=0;j<f[i][1];j++)
                r = ffmul(r,c,2);
        }
        scratch[x0*kover3+y0] = r;
        scratch[y0*kover3+x0] = ffconj(r,2);
    }

    for (x1=0;x1<k;x1++) {
        x0 = (3*x1+e) % kover3;
        for (y1=0;y1<=x1;y1++) {
            y0 = (3*y1+e) % kover3;
            r = scratch[x0*kover3+y0];
            t = (3-e)*(x1-y1)%3;
            if (t == 1)
                r = ffmul(r,Z,2);
            else if (t == 2)
                r = ffmul(r,Zbar,2);
            chi[y1*k+x1] = chi[x1*k+y1] = (r <= 1);
        }
    }

return 27*k; // delete this line once the code has been modified to use m
    return m;
}

// return a list of all admissible residue classes mod zmodulus(k)
// we fill the index and count tables supplied by the caller
// we allocate the residue list
uint32_t admissible(uint16_t **zs,uint16_t *zmodulus,
uint32_t *ztab,uint16_t *zcnts,uint16_t kshort) {
    uint32_t i,j,jmodk,k=kshort,k9,k27,k81,d,e,g,x3,y3,z,z3,b,r,m,n,*bitmap;
    int32_t t,*cbrt_index;
    struct {
        uint32_t cube;
        int32_t next;
    } *table;
    uint16_t *ptr,*res;
    uint8_t *chi;

    k9 = 9*k;
    k27 = 3*k9;
    k81 = 3*k27;
    e = k/3%3;

    n = ((uint64_t)k27*k9+31)>>5;
    table = malloc(k9*sizeof(table[0])+k81*sizeof(cbrt_index[0])
        +n*sizeof(bitmap[0])+k*k);
    cbrt_index = (int32_t *)(table+k9);
    bitmap = (uint32_t *)(cbrt_index+k81);
    chi = (uint8_t *)(bitmap+n);
    m = set_chi(chi,k,bitmap);
    memset(cbrt_index,-1,k81*sizeof(cbrt_index[0]));
    memset(bitmap,0,n*sizeof(bitmap[0]));

    for (t=0,z=e;t<k9;t++,z+=3) {
        z3 = (uint64_t)z*z%k81*z%k81;
        table[t].cube = z3;
        if (z < m) {
            table[t].next = cbrt_index[z3];
            cbrt_index[z3] = t;
        } else
            table[t].next = -1;
    }

    n = 0;
    for (i=0;i<k9;i++) {
        b = i%k*k;
        x3 = table[i].cube;
        for (j=jmodk=0;j<=i;j++,jmodk=modadd(jmodk,1,k))
            if (chi[b+jmodk]) {
                d = modadd(3*i+e,3*j+e,k27);
                g = gcd(d,k);
                if (gcd(g,k/g) > 1) continue;
                y3 = table[j].cube;
                z3 = modsub(modsub(k,x3,k81),y3,k81);
                for (t=cbrt_index[z3];t>=0;t=table[t].next)
                    if (chi[b+t%k] && chi[jmodk*k+t%k]) {
                        r = d*k9+t;
                        if (!(bitmap[r>>5]&(1<<(r&31)))) {
                            bitmap[r>>5]|=(1<<(r&31));
                            n++;
                        }
                        r = (k27-d)*k9+t;
                        if (!(bitmap[r>>5]&(1<<(r&31)))) {
                            bitmap[r>>5]|=(1<<(r&31));
                            n++;
                        }
                    }
            }
    }
    
    ptr = res = malloc(n*sizeof(res[0]));
    for (d=0,r=0;d<k27;d++) {
        ztab[d] = ptr-res;
        for (z=e;z<k27;z+=3,r++)
            if (bitmap[r>>5]&(1<<(r&31)))
                *ptr++ = z;
        zcnts[d] = (ptr-res)-ztab[d];
    }
    free(table);
    *zs = res;
    *zmodulus = m;
    return ptr-res;
}

#ifdef MAIN
#include <stdio.h>
int main(int argc,char *argv[]) {
    uint32_t k,d,i,*k27ztab;
    uint16_t *k27zs,*k27zcnts,m;

    if ( argc < 2 ) { printf ("   admissible k [d]\n"); return 0; }

    sscanf(argv[1],"%u",&k);
    assert (k > 0 && k < 1000 && !(k%3) && (k%9) && (k%8) && (k%125));
    k27ztab = malloc(27*k*sizeof(k27ztab[0]));
    k27zcnts = malloc(27*k*sizeof(k27zcnts[0]));
    admissible(&k27zs,&m,k27ztab,k27zcnts,k);
    if (argc > 2) {
        sscanf(argv[2],"%u",&d);
        for (i=0;i<k27zcnts[d];i++)
            printf("%u\n",k27zs[k27ztab[d]+i]);
    } else {
        for ( d = 0 ; d < 27*k ; d++ ) {
            if ( !(d%3) ) continue;
            printf ("%u:[", d);
            for ( i = 0 ; i < k27zcnts[d] ; i++ ) printf ("%s%u", i?",":"", k27zs[k27ztab[d]+i]);
            printf ("]\n");
        }
    }
    return 0;
}
#endif
