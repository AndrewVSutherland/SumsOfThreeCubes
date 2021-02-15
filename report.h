#ifndef _REPORT_INCLUDE_
#define _REPORT_INCLUDE_

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <gmp.h>
#include "b32.h"
#include "m64.h"
#include "mem.h"
#include "cstd.h"

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

#define VERSION_STRING      "1.1"   // must fit in 8 bytes (including null terminator)

#define CHECKPOINTS         16      // number of intervals, we will only write CHECKPOINTS-1 checkpoints

// This module contains functions for reporting/tracking performance stats and for logging stats and any found solutions to the output file
// Unless REPORT is defined at compile time (see the makefile), reporting will be turned off and only the output_* functions are relevant

#ifndef PROFILE
static inline int profiling (void) { return 0; }
#else
#define PROFILE_RS              (1UL<<25)
static inline int profiling (void) { return 1; }
#endif


double output_start_time;
uint64_t output_start_cycles;

#define PHASE_PRECOMPUTE    0
#define PHASE_CACHED        1   // in this phase p is in cp cache (so cuberoots are precomputed) as are all powers of primes q < p dividing d
#define PHASE_UNCACHED      2   // in this phase p is not in cp cache (so we compute cuberoots) and d/p is not in cd cache
#define PHASE_COCACHED      3   // in this phase d/p is in cd cache (but not sd_cache cuberoots of d/p are precomputed, but not inverses mod d/p)   
#define PHASE_NEARPRIME     4   // in this phase d/p is in sd_cache (so cuberoots and inverses of d/p are precomputed)
#define PHASE_PRIME         5   // in this phase p <= d <= dmax forces d=p
#define PHASE_BIGPRIME      6   // in this phase p <= d <= dmax and p is close enough to zmax that we never split progressions
#define PHASE_MAX           6

#define OPTIONS_NONE        0
#define OPTIONS_PRECOMPUTE  1   // terminate after precomputation is completed
#define OPTIONS_P           2   // just enumerate primes
#define OPTIONS_C           3   // just compute cuberoots modulo prime powers
#define OPTIONS_R           4   // just enumerate arithmetic progressions (d,cbrt(k) mod d) for admissible d not dividing k
#define OPTIONS_Z           5   // count z's in arithmetic progressions we actually check (after applying cubic reciprocity and sieving)
#define OPTIONS_MAX         5

static inline char *option_string (char buf[256], int option)
{
    if ( ! option ) { buf[0] = '\0'; return buf; }
    switch (option) {
        case OPTIONS_PRECOMPUTE: strcpy (buf, ":opt=precompute"); return buf;
        case OPTIONS_P: strcpy (buf, ":opt=enum primes"); return buf;
        case OPTIONS_C: strcpy (buf, ":opt=enum cuberoots"); return buf;
        case OPTIONS_R: strcpy (buf, ":opt=enum progressions"); return buf;
        case OPTIONS_Z: strcpy (buf, ":opt=count sieved zs"); return buf;
        default: sprintf (buf, ":opt=%d unknown", option); return buf;
    }
}

static inline void output (char *buf)
{
    int fd;
    size_t n;

    puts(buf); fflush(stdout);
    fd = open ("output", O_WRONLY | O_CREAT | O_APPEND, 0644);
    if ( fd < 0 ) { fprintf(stderr, "Error writing to output to file!\n"); abort(); } // if we cannot write our output there is no point in continuing
    n = strlen(buf);
    buf[n] = '\n';
    if ( write (fd, buf, n+1) != n+1 )  { close(fd); fprintf(stderr, "Error writing to output to file!\n"); abort(); }
    buf[n] = '\0';
    close (fd);
}

static inline void output_start (int n, int k, uint32_t p0, uint64_t pmin, uint64_t pmax, uint64_t dmax, uint128_t zmax, int opts)
{
    char buf[1024],tbuf[64],obuf[256],zbuf[64],pminbuf[64],pmaxbuf[64];

    output_start_time = get_time();  output_start_cycles = get_cycles();
    if ( p0 > 1 ) { sprintf(pminbuf,"%ux%lu",p0,pmin); sprintf(pmaxbuf,"%ux%lu",p0,pmax); }
    else { sprintf(pminbuf,"%lu",pmin); sprintf(pmaxbuf,"%lu",pmax); }
    sprintf (buf, "START:%s:n=%d:k=%d:pmin=%s:pmax=%s:dmax=%lu:zmax=%s:ver=%s%s",string_time(tbuf),n,k,pminbuf,pmaxbuf,dmax,itoa128(zbuf,zmax),VERSION_STRING,option_string(obuf,opts));
    output(buf);
}

static inline void output_solution (int k, uint64_t d, mpz_t X, mpz_t Y, mpz_t Z)
{
    char buf[1024],tbuf[64];

    gmp_sprintf(buf, "SOLUTION:%s:k=%d:d=%lu:Z=%Zd:*** (%Zd)^3 + (%Zd)^3 + (%Zd)^3 = %d ***",string_time(tbuf),k,d,Z,X,Y,Z,k);
    output(buf);
}

static inline void output_end (int n, int k, uint32_t p0, uint64_t pmin, uint64_t pmax, uint64_t dmax, uint128_t zmax, int opts, int abort)
{
    char buf[1024],tbuf[64],obuf[256],zbuf[64],pminbuf[64],pmaxbuf[64];

    if ( p0 > 1 ) { sprintf(pminbuf,"%ux%lu",p0,pmin); sprintf(pmaxbuf,"%ux%lu",p0,pmax); }
    else { sprintf(pminbuf,"%lu",pmin); sprintf(pmaxbuf,"%lu",pmax); }
    sprintf (buf, "%s:%s:n=%d:k=%d:pmin=%s:pmax=%s:dmax=%lu:zmax=%s:sMB=%.1f:pMB=%.1f:rMB=%.1f:secs=%.1f:ver=%s%s", abort ? "ABORT" : "END",
             string_time(tbuf),n,k,pminbuf,pmaxbuf,dmax,itoa128(zbuf,zmax),(double)shared_bytes()/(1<<20),(double)private_bytes()/(1<<20),(double)get_maxrss()/(1<<10),get_time()-output_start_time,VERSION_STRING,option_string(obuf,opts));
    output(buf);
}


#ifndef VERBOSE
static inline void verbose_printf (const char *format, ...) {}
#else
static inline void verbose_printf (const char *format, ...) { va_list args; va_start(args, format); vprintf(format, args); va_end(args); }
#endif  

// REPORT should be defined at compile time in the makefile
#ifndef REPORT 

// these should all get compiled into oblivion and have zero overhead unless REPORT is defined
static inline int reporting(void) { return 0; }
static inline int report_options(void) { return 0; }
static inline void report_timer_reset () {}
static inline double report_timer_elapsed () { return 0.0; }
static inline void report_printf (const char *format, ...) {}
static inline uint64_t report_start (int cores, int k, uint32_t p0, uint64_t pmin, uint64_t pmax, uint64_t dmax, long double zmax, int opts)
    { assert (!opts); return pmin; }
static inline void report_reset (unsigned n) {}
static inline int report_phase (int phase) { return 1; }
static inline void report_job_start (unsigned job) {}
static inline void report_job_end (unsigned job) {}
static inline void report_comparisons (uint64_t ppcnt, uint64_t pccnt, uint64_t pdcnt, uint64_t prcnt) {}
static inline void report_end (void) {}

static inline int report_p (uint64_t p) { return 1; }
static inline int report_c (uint32_t n) { return 1; }
static inline int report_d (uint64_t d, uint32_t n) { return 1; }
static inline int report_z (uint64_t d, uint64_t n, uint64_t l, uint32_t i) { return 1; }
static inline void report_zpass (uint128_t absz) {}
static inline void report_zcheck (uint128_t absz) {}
static inline void report_s (uint64_t d, uint128_t absz) {}

static inline void profile_start (void) {}
static inline void profile_checkpoint (void) {}
static inline void profile_end (void) {}
static inline void profile_zrcheck_start (void) {}
static inline void profile_zrcheck_setup (void) {}
static inline void profile_zrcheck_end (void) {}
static inline void profile_zrlift_start (void) {}
static inline void profile_zrlift_end (void) {}

#else

#define PBITS 28    // only relevant for OPTION_P
#define CBITS 28    // only relevant for OPTION_C 
#define RBITS 25
#define ZBITS 29
#define ZRMAX 1000000000.0

char *phases[] = { "precomputation", "cached", "uncached", "cocached", "nearprime", "prime", "bigprime", "final" };

static double adhoc_timer;  // used by report_reset, report_elapsed
static uint64_t pcnt, rpcnt, ppcnt, ccnt, rccnt, pccnt, dcnt, rdcnt, pdcnt, rcnt, rrcnt, prcnt, pcur, zcnt, rzcnt, pzcnt, zccnt, zlcnt, zmcnt, zmpzcnt, bytes;
static uint64_t zchks[3];
static uint32_t report_k, report_p0, scnt;
static uint64_t report_pmin, report_pmax, report_dmax, phase_lines;
static uint128_t report_zmax, zmsum;
static long double report_zmaxld;
static int options, current_phase;
static double start_time, report_time, phase_time, precompute_time;
static uint64_t start_cycles, report_cycles, phase_cycles;
static uint32_t jobs, jobid;
static int pbits, cbits, rbits, zbits;

// Do not make any changes to this structure without changing the version number (otherwise checkpoints will be broken)
struct jobstat_rec {
    char version[8];
    uint32_t jobs, jobid, k, p0;
    uint64_t pmin, pmax, dmax;
    uint128_t zmax;
    uint64_t pcnt, ccnt, dcnt, rcnt, zcnt, zccnt, zlcnt, zmcnt, zmpzcnt, zchks[3], cycles, bytes, maxrss;
    uint128_t zmsum;
    double secs;
    uint32_t scnt, chkpt_id;
    uint64_t chkpt_pmax;
} *jobstats;                                // this will point to shared memory

static uint32_t chkpt_id, num_chkpts;       // num_checkpts is typically CHECKPOINTS but my be smaller depending in (pmin,pmax)
static uint64_t chkpt_pmax[CHECKPOINTS+1];  // entry 0 reserved for null, nth checkpoint covers p in [pmin,chkpt_max[n]], chkpt_max[CHECKPOINTS] = pmax is a sentinel

void init_jobstats (struct jobstat_rec *x, uint32_t job)
{
    memset (x,0,sizeof(*x));
    memcpy(x->version,VERSION_STRING,sizeof(VERSION_STRING));
    x->jobs = jobs; x->jobid = job; x->k = report_k; x->p0 = report_p0;
    x->pmin = report_pmin; x->pmax = report_pmax; x->dmax = report_dmax; x->zmax = report_zmax;
}

void update_jobstats (struct jobstat_rec *x)
{
    assert ( memcmp(x->version,VERSION_STRING,sizeof(VERSION_STRING)) == 0 );
    assert ( x->jobs == jobs && x->jobid == jobid && x->k == report_k && x->p0 == report_p0 );
    assert ( x->pmin == report_pmin && x->pmax == report_pmax && x->dmax == report_dmax && x->zmax == report_zmax );
    x->pcnt += pcnt; x->ccnt += ccnt; x->dcnt += dcnt; x->rcnt += rcnt; x->zcnt += zcnt; x->zccnt += zccnt; x->zlcnt += zlcnt; x->zmsum += zmsum;
    x->zchks[0] += zchks[0]; x->zchks[1] += zchks[1]; x->zchks[2] += zchks[2]; 
    x->zmcnt += zmcnt; x->zmpzcnt += zmpzcnt; x->bytes = _max(x->bytes,private_bytes()); x->maxrss = _max(x->maxrss,get_maxrss());
    x->cycles += get_cycles()-start_cycles;  x->secs += get_time()-start_time;
    x->scnt += scnt;
    x->chkpt_id = chkpt_id;
    x->chkpt_pmax = chkpt_pmax[chkpt_id];
}

static inline char *checkpoint_file (char *buf, uint32_t job, uint32_t chkpt)
    { sprintf (buf, "checkpoint_%u_%u", job, chkpt); return buf; }

static void write_checkpoint ()  // writes current checkpoint for current job
{
    FILE *fp;
    struct jobstat_rec rec;
    char buf[32];
    size_t cnt;

    verbose_printf ("Writing checkpoint %d (pmax=%lu) for job %d at p=%lu\n", chkpt_id, chkpt_pmax[chkpt_id], jobid, pcur);

    assert (chkpt_id && chkpt_id < num_chkpts && pcur <= chkpt_pmax[chkpt_id]);
    rec = jobstats[jobid];
    update_jobstats (&rec); // update copy, not jobstats[jobid] because we are not clearing counters, they will get applied again
    fp = fopen (checkpoint_file(buf,jobid,chkpt_id),"wb"); assert(fp); cnt = fwrite(&rec, sizeof(rec), 1, fp); fclose(fp);  assert (cnt==1);
    chkpt_id++;
}

// reads specified checkpoint for specified job, returns 1 if found, 0 if no checkpoint file exists, -1 if anything looks fishy
static int read_checkpoint (struct jobstat_rec *x, uint32_t job, uint32_t chkpt)
{
    FILE *fp;
    char buf[32];
    size_t cnt;

    assert (job < jobs && chkpt && chkpt < num_chkpts);
    fp = fopen (checkpoint_file(buf,job,chkpt),"rb");  if ( !fp ) return 0;
    cnt = fread(x, sizeof(*x), 1, fp); fclose(fp);
    if (cnt != 1) return -1;
    if ( memcmp(x->version,VERSION_STRING,sizeof(VERSION_STRING)) != 0 ) return -1;
    if ( x->jobs != jobs || x->jobid != job || x->chkpt_id != chkpt || x->chkpt_pmax != chkpt_pmax[chkpt] ) return -1;
    if ( x->k != report_k || x->p0 != report_p0 || x->pmin != report_pmin || x->pmax != report_pmax || x->dmax != report_dmax || x->zmax != report_zmax ) return -1;
    return 1;
}

static void delete_checkpoint (uint32_t job, uint32_t chkpt)
    { char buf[32]; remove(checkpoint_file(buf,job,chkpt)); }


static inline void report_printf (const char *format, ...) { va_list args;  va_start(args, format);  vprintf(format, args);  va_end(args); fflush(stdout); }

static inline int reporting(void) { return 1; }
static inline int report_options(void) { return options; }
static inline void report_timer_reset () { adhoc_timer = get_time(); }
static inline double report_timer_elapsed () { return get_time()-adhoc_timer; }


static inline int goodp (uint64_t k, uint64_t p)
    { return ( (p>k || (k%p)) && (mod3(p)!=1 || m64_has_cbrts(m64_from_ui(k,p),m64_R(p),p,m64_pinv(p))) ); }

static inline uint64_t report_start (int cores, int k, uint32_t p0, uint64_t pmin, uint64_t pmax, uint64_t dmax, uint128_t zmax, int opts)
{
    char buf[1024], obuf[64], tbuf[64], zbuf[64], pminbuf[64], pmaxbuf[64], spminbuf[64];
    uint64_t p,start_pmin;
    int i,j,sts;

    assert (cores && opts <= OPTIONS_MAX && zmax);
    if ( profiling() ) assert (cores==1);
#if VERIFY
report_printf ("VERIFICATION:1\n");
#endif
    if ( opts ) { char obuf[64]; report_printf ("OPTIONS%s\n", option_string(obuf,opts)); }
    pbits = PBITS;
    cbits = CBITS;
    rbits = RBITS + (opts==OPTIONS_R?_min(dmax/pmax+1,5):0);
    zbits = ZBITS + (opts==OPTIONS_Z?6:0);
    options = opts;
    report_k = k; report_p0 = p0; report_pmin = pmin; report_pmax = pmax; report_dmax = dmax; report_zmax = zmax; report_zmaxld = (long double)zmax+(zmax>>52)+1;

    // compute checkpoint intervals -- this should be a deterministic function of (pmin,pmax) and if there is more than one each should contain a good prime
    if ( pmin < 2 ) pmin = 2;
    assert ( pmin <= pmax );
    chkpt_pmax[0] = p = pmin-1;  num_chkpts = 0;
    while ( num_chkpts < CHECKPOINTS-1 ) {
        p = p + (pmax-p)/(CHECKPOINTS-num_chkpts);  // partition linearly rather than exponentially (for large runs pmin and pmax will be close together)
        for ( p = primes_next_prime (p) ; !goodp(k,p) ; p = primes_next_prime(p) );   // make sure there is at least one good prime in the checkpoint interval
        if ( p >= pmax ) break;
        assert (p > chkpt_pmax[num_chkpts]);
        chkpt_pmax[++num_chkpts] = p;
    }
    chkpt_pmax[++num_chkpts] = pmax;    // sentinel, we will never actually checkpoint the last interval
    if ( num_chkpts==1 ) {
        report_printf ("Only one checkpointing interval -- this means no checkpointing.\n");
    } else {
        report_printf ("Using %d checkpoint intervals: ", num_chkpts);
        for ( i = 1 ; i < num_chkpts-1 ; i++ ) report_printf ("%lu, ", chkpt_pmax[i]);
        report_printf ("%lu\n", chkpt_pmax[i]);
    }

    jobs = cores;
    jobstats = shared_malloc (jobs*sizeof(*jobstats));

    // search for last checkpoint written by every job (if any)
    for ( j = 1 ; j < num_chkpts ; j++ ) {
        for ( i = 0 ; i < jobs ; i++ ) {
            if ( ! (sts = read_checkpoint (jobstats+i, i, j)) ) break;
            if ( sts < 0 ) { report_printf ("Deleting inconsistent checkpoint file %s\n", checkpoint_file(buf,i,j)); delete_checkpoint(i,j);  break; }
        }
        if ( i < jobs ) break;
    }
    // if j > 1 then we have a checkpoint we can restart from
    if ( --j ) {
        double restart_secs = 0.0;
        uint64_t restart_pcnt=0, restart_ccnt=0, restart_dcnt=0, restart_rcnt=0, restart_zcnt=0, restart_cycles=0;

        chkpt_id = j;
        for ( i = 0 ; i < jobs ; i++ ) {
            sts = read_checkpoint (jobstats+i, i, chkpt_id); assert (sts == 1);
            restart_pcnt += jobstats[i].pcnt; restart_ccnt += jobstats[i].ccnt; restart_dcnt += jobstats[i].dcnt; restart_rcnt += jobstats[i].rcnt;
            restart_zcnt += jobstats[i].zcnt; restart_cycles += jobstats[i].cycles; restart_secs += jobstats[i].secs; 
        }
        start_pmin = chkpt_pmax[chkpt_id]+1;
        chkpt_id++;
        assert (start_pmin <= chkpt_pmax[chkpt_id]);
        if ( report_p0 > 1 ) { sprintf(pminbuf,"%ux%lu",report_p0,pmin); sprintf(spminbuf,"%ux%lu",report_p0,start_pmin); sprintf(pmaxbuf,"%ux%lu",report_p0,pmax); }
        else { sprintf(pminbuf,"%lu",pmin); sprintf(spminbuf,"%lu",start_pmin); sprintf(pmaxbuf,"%lu",pmax); }
        string_time(tbuf); option_string(obuf,options);
        sprintf (buf, "RESTART:%s:n=%d:k=%d:pmin=%s:pmax=%s:dmax=%lu:zmax=%s:restart_pmin=%s:cyc=%lu:pcnt=%lu:ccnt=%lu:dcnt=%lu:rcnt=%lu:zcnt=%lu:secs=%.1f:ver=%s%s",
                 tbuf,jobs,k,pminbuf,pmaxbuf,dmax,itoa128(zbuf,zmax),spminbuf,restart_cycles,restart_pcnt,restart_ccnt,restart_dcnt,restart_rcnt,restart_zcnt,restart_secs,VERSION_STRING,obuf);
        output (buf);
    } else {
        for ( i = 0 ; i < jobs ; i++ ) init_jobstats(jobstats+i,i);
        chkpt_id = 1;
        start_pmin = pmin;
    }
    // IMPORTANT: we need to clear any extra checkpoint files to avoid possible inconsistencies in the future
    // We cannot assume the same jobs will get the same primes in our new run (this almost surely will not happen)
    for ( i = 0 ; i < jobs ; i++ ) for ( j = chkpt_id ; j < num_chkpts ; j++ ) delete_checkpoint(i,j);
    start_time = report_time = phase_time = get_time();  start_cycles = report_cycles = phase_cycles = get_cycles();
    return start_pmin;
}

static inline void report_job_start (unsigned job)
{
    assert (job < jobs);
    jobid = job;
    pcnt = rpcnt = ppcnt = 0;  pcur = 0;
    ccnt = rccnt = pccnt = 0;
    dcnt = rdcnt = pdcnt = 0;
    rcnt = rrcnt = prcnt = 0;
    zcnt = rzcnt = pzcnt = 0;
    zccnt = zlcnt = zmcnt = zmpzcnt = 0;
    zmsum = 0;
    memset(zchks,0,sizeof(zchks));
    start_time = report_time = phase_time = get_time();
    start_cycles = report_cycles = phase_cycles = get_cycles();
}

static inline void report_job_end (unsigned job)
{
    char tbuf[64], obuf[64], zbuf[64], zmbuf[64], pminbuf[64], pmaxbuf[64];
    assert (job == jobid);
    struct jobstat_rec *x = jobstats+jobid;
    update_jobstats (x);
    if ( report_p0 > 1 ) { sprintf(pminbuf,"%ux%lu",report_p0,report_pmin); sprintf(pmaxbuf,"%ux%lu",report_p0,report_pmax); }
    else { sprintf(pminbuf,"%lu",report_pmin); sprintf(pmaxbuf,"%lu",report_pmax); }
    string_time(tbuf); option_string(obuf,options);
    verbose_printf ("JOBSTATS:%s:n=%d:k=%d:pmin=%s:pmax=%s:dmax=%lu:zmax=%s:job=%d:cyc=%lu:pcnt=%lu:ccnt=%lu:dcnt=%lu:rcnt=%lu:zcnt=%lu:zccnt=%lu:zlcnt=%lu:zchk1=%lu:zhck2=%lu:zchk0=%lu:zmcnt=%lu:zmpzcnt=%lu:zmsum=%s:sMB=%.1f:pMB=%.1f:rMB=%.1f:secs=%.1f:cyc/p=%.0f:cyc/r=%.0f:cyc/z=%.0f:scnt=%u:ver=%s%s\n",
                   tbuf,jobs,report_k,pminbuf,pmaxbuf,report_dmax,itoa128(zbuf,report_zmax),jobid,x->cycles,x->pcnt,x->ccnt,x->dcnt,x->rcnt,x->zcnt,x->zccnt,x->zlcnt,x->zchks[1],x->zchks[2],x->zchks[0],x->zmcnt,x->zmpzcnt,itoa128(zmbuf,x->zmsum),(double)shared_bytes()/(1<<20),(double)x->bytes/(1<<20),(double)x->maxrss/(1<<10),
                   x->secs,(double)x->cycles/x->pcnt,(double)x->cycles/x->rcnt,(double)x->cycles/x->zcnt,x->scnt,VERSION_STRING,obuf);
}

static inline void pad (char buf[], int n)
    { int i = n-strlen(buf); if ( i>0 ) { memmove(buf+i,buf,strlen(buf)+1); memset(buf,' ',i); } else { memmove(buf+1,buf,strlen(buf)+1); buf[0] = ' '; } }

static inline void print_counters (uint64_t xcyc, double xtime, uint64_t xpcnt, uint64_t xccnt, uint64_t xdcnt, uint64_t xrcnt, uint64_t xzcnt)
{
    char pbuf[64], cbuf[64], dbuf[64], rbuf[64], zbuf[64], progbuf[64], sbuf[64], tbuf[64];
    uint64_t c,cyc,tcyc,x;
    double t;

    c = get_cycles(); cyc = c-xcyc;  tcyc = c-start_cycles;  t = get_time();
    x=pcnt-xpcnt; sprintf(pbuf,"%lu (%.0f)", x, (double)cyc/x); pad(pbuf,20);
    x=ccnt-xccnt; sprintf(cbuf,"%lu (%.0f)", x, (double)cyc/x); pad(cbuf,20);
    x=dcnt-xdcnt; sprintf(dbuf,"%lu (%.0f)", x, (double)cyc/x); pad(dbuf,20);
    x=rcnt-xrcnt; sprintf(rbuf,"%lu (%.0f)", x, (double)cyc/x); pad(rbuf,20);
    x=zcnt-xzcnt; sprintf(zbuf,"%lu (%.1f)", x, (double)cyc/x); pad(zbuf,24);
    if ( report_p0 == 1 ) sprintf(progbuf,"%lu",pcur); else sprintf(progbuf,"%u*%lu",report_p0,pcur);
    pad(progbuf,18);
    sprintf(sbuf,"%.0f cyc/r", (double)tcyc/rcnt); pad(sbuf,24);
    sprintf (tbuf,"[%3.1fs]", t-xtime);  pad(tbuf,9);
    report_printf ("%s%s%s%s%s%s%s%s\n", pbuf, cbuf, dbuf, rbuf, zbuf, tbuf, progbuf, sbuf);
}

static inline void report_line (void)
{
    if ( jobs && jobid != jobs-1 ) return;
    print_counters (report_cycles, report_time, rpcnt, rccnt, rdcnt, rrcnt, rzcnt);
    rpcnt = pcnt; rccnt = ccnt; rdcnt = dcnt; rrcnt = rcnt; rzcnt = zcnt;  report_time = get_time(); report_cycles = get_cycles();
    phase_lines++;
}

static inline int report_phase (int n)
{
    double t;

    if ( profiling() ) return 1;
    assert (n >= 0 && n <= PHASE_MAX);
    if ( n < PHASE_MAX ) current_phase = n+1;
    t = get_time();
    if ( !n ) { 
        report_printf ("Completed %s phase in %.1fs.\n", phases[n], t-phase_time);
        precompute_time = t-start_time;
        start_time = report_time = phase_time = t;
        start_cycles = report_cycles = phase_cycles = get_cycles();
        return options != OPTIONS_PRECOMPUTE;
    }
    if ( jobs && jobid != jobs-1 ) return 1;
    if ( pcnt == ppcnt && n && n < PHASE_MAX ) { report_printf ("Nothing to do in %s phase.\n", phases[n]); return 1; }
    if ( phase_lines ) { char buf[256]; memset(buf,'-',156); buf[156] = '\0'; report_printf ("%s\n",buf); }
    print_counters (phase_cycles, phase_time, ppcnt, pccnt, pdcnt, prcnt, pzcnt);
    report_printf ("Completed %s phase in %.1fs.\n", phases[n], t-phase_time);
    rpcnt = ppcnt = pcnt; rccnt = pccnt = ccnt; rrcnt = prcnt = rcnt; rdcnt = pdcnt = dcnt; rzcnt = pzcnt = zcnt;
    report_time = phase_time = get_time(); report_cycles = phase_cycles = get_cycles();
    phase_lines = 0;
    return 1;
}

static inline void report_end (void)
{
    double total_time, max_time;
    uint64_t total_cycles, maxrss;
    char buf[1024],tbuf[64],obuf[256],zbuf[64],zmbuf[64],pminbuf[64],pmaxbuf[64];

    if ( report_p0 > 1 ) { sprintf(pminbuf,"%ux%lu",report_p0,report_pmin); sprintf(pmaxbuf,"%ux%lu",report_p0,report_pmax); }
    else { sprintf(pminbuf,"%lu",report_pmin); sprintf(pmaxbuf,"%lu",report_pmax); }
    string_time(tbuf); option_string(obuf,options);
    pcnt = ccnt = dcnt = rcnt = zcnt = zccnt = zlcnt = zmcnt = zmpzcnt = bytes = maxrss = 0;
    total_cycles = 0; total_time = max_time = 0.0;
    scnt = 0;
    for ( int i = 0 ; i < jobs ; i++ ) {
        struct jobstat_rec *x = jobstats+i;
        pcnt += x->pcnt; ccnt += x->ccnt; dcnt += x->dcnt; rcnt += x->rcnt; zcnt += x->zcnt; zccnt += x->zccnt; zlcnt += x->zlcnt; zmcnt += x->zmcnt; zmsum += x->zmsum; zmpzcnt += x->zmpzcnt;
        zchks[0] += x->zchks[0];  zchks[1] += x->zchks[1];  zchks[2] += x->zchks[2];
        total_cycles += x->cycles; total_time += x->secs; bytes += x->bytes; maxrss += x->maxrss;
        scnt += x->scnt;
        if ( x->secs > max_time ) max_time = x->secs;
    }
    uint64_t c = total_cycles;
    report_printf ("   pcnt: %20lu (%.0f cyc/p)\n", pcnt, (double)c/pcnt);
    report_printf ("   ccnt: %20lu (%.0f cyc/c)\n", ccnt, (double)c/ccnt);
    report_printf ("   dcnt: %20lu (%.0f cyc/d)\n", dcnt, (double)c/dcnt);
    report_printf ("   rcnt: %20lu (%.0f cyc/r) (%.1f r/d, %.1f r/c, %.1f r/p)\n", rcnt, (double)c/rcnt, (double)rcnt/dcnt, (double)rcnt/ccnt, (double)rcnt/pcnt);
    report_printf ("   zcnt: %20lu (%.1f cyc/z) (%.1f z/r) (%.1f z/d)\n", zcnt, (double)c/zcnt, (double)zcnt/rcnt, (double)zcnt/dcnt);
    report_printf ("  zccnt: %20lu (%.1f zc/r) (%.1f zc/d)\n", zccnt, (double)zccnt/rcnt, (double)zccnt/dcnt);
    report_printf ("  zlcnt: %20lu (%.1f zl/r) (%.1f zl/d)\n", zlcnt, (double)zlcnt/rcnt, (double)zlcnt/dcnt);
    report_printf ("  zmcnt: %20lu (1/%.1f mp/z)\n", zmcnt, (double)zcnt/zmcnt);
    report_printf ("zmzpcnt: %20lu (1/%.1f mpz/z)\n", zmpzcnt, (double)zcnt/zmpzcnt);
    max_time += precompute_time;
    report_printf ("Total job cputime: %.1f secs, %.1f gcycs, Precompute cputime: %.1fs, Total wall time: %.1fs\n", total_time, total_cycles/1000000000.0, precompute_time, get_time()-start_time);
    sprintf (buf, "STATS:%s:n=%d:k=%d:pmin=%s:pmax=%s:dmax=%lu:zmax=%s:cyc=%lu:pcnt=%lu:ccnt=%lu:dcnt=%lu:rcnt=%lu:zcnt=%lu:zccnt=%lu:zlcnt=%lu:zchk1=%lu:zchk2=%lu:zchk0=%lu:zmcnt=%lu:zmpzcnt=%lu:zmsum=%s:sMB=%.1f:pMB=%.1f:rMB=%.1f:secs=%.1f:psec=%.1f:wsecs=%.1f:cyc/p=%.0f:cyc/r=%.0f:cyc/z=%.1f:scnt=%u:ver=%s%s",
            string_time(tbuf),jobs,report_k,pminbuf,pmaxbuf,report_dmax,itoa128(zbuf,report_zmax),total_cycles,pcnt,ccnt,dcnt,rcnt,zcnt,zccnt,zlcnt,zchks[1],zchks[2],zchks[0],zmcnt,zmpzcnt,itoa128(zmbuf,zmsum),(double)shared_bytes()/(1<<20),(double)bytes/(1<<20),(double)maxrss/(1<<10),
            total_time,precompute_time,max_time,(double)total_cycles/pcnt,(double)total_cycles/rcnt,(double)total_cycles/zcnt,scnt,VERSION_STRING,obuf);
    output (buf);
    // clean up checkpoint files
    for ( int i = 0 ; i < jobs ; i++ ) for ( int j = 1 ; j < num_chkpts ; j++ ) delete_checkpoint (i,j);
}

static inline void report_comparisons (uint64_t cpcnt, uint64_t cccnt, uint64_t cdcnt, uint64_t crcnt)
{
    char buf[1024],tbuf[64],zbuf[64],pminbuf[64],pmaxbuf[64];
    if ( report_p0 > 1 ) { sprintf(pminbuf,"%ux%lu",report_p0,report_pmin); sprintf(pmaxbuf,"%ux%lu",report_p0,report_pmax); }
    else { sprintf(pminbuf,"%lu",report_pmin); sprintf(pmaxbuf,"%lu",report_pmax); }
    string_time(tbuf);
    sprintf (buf, "CSTATS:%s:n=%d:k=%d:pmin=%s:pmax=%s:dmax=%lu:zmax=%s:pcnt=%lu:ccnt=%lu:dcnt=%lu:rcnt=%lu:cpcnt=%lu:cccnt=%lu:cdcnt=%lu:crcnt=%lu:ver=%s",
             string_time(tbuf),jobs,report_k,pminbuf,pmaxbuf,report_dmax,itoa128(zbuf,report_zmax),pcnt,ccnt,dcnt,rcnt,cpcnt,cccnt,cdcnt,crcnt,VERSION_STRING);
    output(buf);
}

static inline int report_p (uint64_t p)
{
    softassert (p > pcur && p <= report_pmax);
    // Note that prime_pipe can skip over an entire checkpoint interval (other threads may have processed all the primes)
    // But we are guaranteed to see primes in increasing order.
    while ( p > chkpt_pmax[chkpt_id] ) write_checkpoint();
    pcur = p; if ( report_p0 == 1 || p == report_p0 ) pcnt++;
    if ( options == OPTIONS_P ) { if ( (pcnt-rpcnt) >> pbits ) report_line (); return 0; }
    return 1;
}

static inline int report_c (uint32_t n)
{
    ccnt += n;
    if ( options == OPTIONS_C ) { if ( (ccnt-rccnt) >> cbits ) report_line (); return 0; }
    return 1;
}

static inline int report_d (uint64_t d, uint32_t n)
{
    if ( (rcnt-rrcnt) >> rbits  ) report_line ();
    dcnt++; rcnt += n;
    return ( options != OPTIONS_R );
}

static inline void report_s (uint64_t d, uint128_t absz)
{
    scnt++;
}

static inline int report_z (uint64_t d, uint64_t n, uint64_t l, uint32_t location)   // 1=checkone, 2=checkafew, 0=checkmany
{
    softassert(location<3);
    if ( (zcnt-rzcnt) >> zbits ) report_line ();
    uint64_t zs = n*l;
    zcnt += zs;  zccnt += n; zlcnt += l;
    zchks[location]++;
//  if ( zs > ZRMAX ) verbose_printf ("Processing %lu z's for d=%lu...\n", zs, d);
    return ( options != OPTIONS_Z );
}

static inline void report_zpass (uint128_t absz) { zmcnt++; zmsum += absz; }
static inline void report_zcheck (uint128_t absz) { zmpzcnt++; }

#ifndef PROFILE

static inline void profile_start () {}
static inline void profile_checkpoint () {}
static inline void profile_end () {}
static inline void profile_zrcheckone (void) {}
static inline void profile_zrcheck_start (void) {}
static inline void profile_zrcheck_setup (void) {}
static inline void profile_zrcheck_end (void) {}
static inline void profile_zrlift_start (void) {}
static inline void profile_zrlift_end (void) {}

#else

// Each call to get_cycles() burns on the order of 20 cycles, use these sparingly
// Currently we only profile zrchecklift, zrcheckmany

static uint64_t zrcheck_cnt, zrlift_cnt, zrcheck_cycles, zrcheck_setup_cycles, zrlift_cycles;
static uint64_t zrcheck_cycler, zrcheck_cycles, zrlift_cycler, zrlift_cycles;

static inline void profile_start (void)
{ report_job_start (0); }

static inline void profile_zrcheck_start (void) { zrcheck_cnt++; zrcheck_cycler = get_cycles(); }
static inline void profile_zrcheck_setup (void) { zrcheck_setup_cycles += get_cycles()-zrcheck_cycler; }
static inline void profile_zrcheck_end (void) { zrcheck_cnt++; zrcheck_cycles += get_cycles()-zrcheck_cycler; }
static inline void profile_zrlift_start (void) { zrlift_cycler = get_cycles(); }
static inline void profile_zrlift_end (void) { zrlift_cnt++; zrlift_cycles += get_cycles()-zrlift_cycler; }

static inline void profile_end (void)
{
    char buf[1024],tbuf[64], obuf[64], zbuf[64];
    report_job_end (0);
    report_printf (" chk1cnt: %19lu\n", zchks[1]);
    report_printf (" chk2cnt: %19lu\n", zchks[2]);
    report_printf (" chk0cnt: %19lu\n", zchks[0]);
    report_printf ("  chkcnt: %19lu (%.1f cyc/d) (%.1f cyc/setup) (%.1f cyc/z)\n", zrcheck_cnt, (double)zrcheck_cycles/zrcheck_cnt, (double)zrcheck_setup_cycles/zrcheck_cnt, (double)zrcheck_cycles/zcnt);
    report_printf (" liftcnt: %19lu (%.1f cyc/d) (%.1f cyc/z)\n", zrlift_cnt, (double)zrlift_cycles/zrlift_cnt, (double)zrlift_cycles/zcnt);
    report_end();
    sprintf (buf, "PROFILE:%s:n=%d:k=%d:pmin=%lu:pmax=%lu:dmax=%lu:zmax=%s:rcnt=%lu:zcnt=%lu:zccnt=%lu:zlcnt=%lu:zmcnt=%lu:zmpzcnt=%lu:zrliftcnt=%lu:zrcheckcnt=%lu:zrcheckcycs=%lu:zrsetupcycs=%lu:zrliftcycs=%lu%s",
            string_time(tbuf),jobs,report_k,report_pmin,report_pmax,report_dmax,itoa128(zbuf,report_zmax),rcnt,zcnt,zccnt,zlcnt,zmcnt,zmpzcnt,zrlift_cnt,zrcheck_cnt,zrcheck_cycles,zrcheck_setup_cycles,zrlift_cycles,option_string(obuf,options));
    output (buf);
    output_end (jobs, report_k, report_p0, report_pmin, report_pmax, report_dmax, report_zmax, options, 1);
    exit(0);
}

static inline void profile_checkpoint ()
    { if ( rcnt >= PROFILE_RS ) profile_end (); }

#endif

#endif

#endif
