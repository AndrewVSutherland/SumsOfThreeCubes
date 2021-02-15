#ifndef _PRIMES_INCLUDE_
#define _PRIMES_INCLUDE_

/*
    Copyright (c) 2019 Andrew V. Sutherland
    See LICENSE file for license details.
*/

#include <stdlib.h>
#include <math.h>
#include <semaphore.h>
#include <primesieve.h>
#include "mem.h"
#include "cstd.h"

/*
    Interface to primesieve, also provides a prime pipe for parallel processing
*/

#define PRIMES_SMALL_BOUND      (1<<13)
#define PRIMES_SMALL_COUNT      6542

#ifndef PRIMES_PRIVATE
extern uint16_t _primes_small_primes[PRIMES_SMALL_COUNT+1];
extern uint16_t _primes_small_indexes[PRIMES_SMALL_BOUND+1];
#endif

typedef primesieve_iterator primes_ctx_t;

static inline primes_ctx_t *primes_enum_start (uint64_t start, uint64_t end)
{
    primesieve_iterator *it = malloc(sizeof(*it));
    primesieve_init(it);
    if ( end >= start ) {
        // note primesize iterates p > start but we do p >= start
        if ( start > 2 ) primesieve_skipto (it, start-1, end);
    } else {
        primesieve_skipto (it, start+1, end);
    }
    return (primes_ctx_t*)it;
}

static inline uint64_t primes_enum_next (primes_ctx_t *ctx) { return primesieve_next_prime(ctx); }
static inline uint64_t primes_enum_prev (primes_ctx_t *ctx) { return primesieve_prev_prime(ctx); }
static inline void primes_enum_end (primes_ctx_t *ctx) { primesieve_free_iterator(ctx); free(ctx); }

#define PRIMES_PIPE_MAX_READERS     (1<<10)
#define PRIMES_PIPE_MAX_BUFSIZE     (1<<30)
#define PRIMES_PIPE_DEFAULT_BUFSIZE (1<<16)
#define PRIMES_PIPE_DEFAULT_LATENCY (1UL<<30)       // in cycles, this should be about 1/3 of a second
#define PRIMES_DONE                 (~(uint64_t)0)

typedef struct primes_pipe {
    uint64_t start;                     // primes in [start,end]
    uint64_t end;                       // will be enumerated
    volatile uint64_t high;             // largest prime enumerated (if >= end we are done), set by writer read by readers
    uint32_t bufsize;                   // number of elements in the arrary pointed to each readers[i]->primes
    uint32_t num_readers;               // number of readers (forked children)
    uint64_t latency;                   // target latency (number of cycles between calls to primes_read_pipe)
    sem_t hungry_readers;               // feeder waits on this, readers post when ready for more primes
    sem_t finished_readers;             // readers post to this when they close the pipe, feeder waits on this when destroying the pipe
    primes_ctx_t *ctx;                  // prime enumerator used by writer, created on first call to feed_pipe (readers should fork before this)
    struct primes_pipe_reader {
        sem_t good_to_go;               // feeder posts to this when primes for this reader are ready, reader waits on it
        volatile uint32_t want_primes;  // set by reader to request more primes, read/reset by feeder
        volatile uint32_t num_primes;   // set by feeder when primes are ready, read by reader
        volatile uint32_t read_primes;  // updated by reader as primes are ready, reset by feeeder
        volatile uint32_t finished;     // set by reader when pipe is closed, sanity checked by feeder when pipe is destroyed
        clock_t last;                   // cycle count when reader began the most recent batch, used to manage latency (private to reader)
        volatile uint64_t *primes;      // pointer to array of primes for this reader to process (written by writer, read by reader)
    } readers[];                        // reader array starts immediately after prime_pipe_struct (all of this is in shared memory)
} primes_pipe_ctx_t;

// set bufsize and/or latency to 0 to use defaults
primes_pipe_ctx_t *_primes_create_pipe (uint64_t start, uint64_t end, uint32_t readers, uint32_t bufsize, uint64_t latency);
static inline primes_pipe_ctx_t *primes_create_pipe (uint64_t start, uint64_t end, uint32_t readers, uint32_t bufsize, uint64_t latency)
{
    // readers=0 forces pass through to primes_enum, no need to buffer/synchronize anything
    if ( !readers )
        { struct primes_pipe *pipe = private_calloc(sizeof(*pipe)); pipe->start = start; pipe->end = end; pipe->ctx = primes_enum_start(start,end); return pipe; }
    return _primes_create_pipe (start,end,readers,bufsize,latency);
}
void _primes_destroy_pipe (primes_pipe_ctx_t *pipe);
static inline void primes_destroy_pipe (primes_pipe_ctx_t *pipe)
    { if ( !pipe->num_readers ) private_free (pipe,sizeof(*pipe)); else _primes_destroy_pipe (pipe); }

// returns a prime in [pipe->start,pipe->end] or PRIMES_DONE > pipe->end, primes will be in increasing order (but no guarantees otherwise)
static inline uint64_t primes_read_pipe (primes_pipe_ctx_t *pipe, uint32_t i)
{
    if ( !pipe->num_readers ) return ( pipe->high < pipe->end && (pipe->high = primes_enum_next(pipe->ctx)) <= pipe->end ? pipe->high : PRIMES_DONE );
    softassert (i < pipe->num_readers);
    struct primes_pipe_reader *x = pipe->readers+i;
    if ( x->read_primes < x->num_primes ) return x->primes[x->read_primes++];
    if ( pipe->high >= pipe->end ) return PRIMES_DONE;
    uint64_t t = get_cycles() - x->last;
    if ( !(t>>63) ) {           // ignore the cycle count if it went backwards (this is possible on older or multi-cpu systems)
        if ( t < pipe->latency/2 && x->num_primes && x->num_primes < pipe->bufsize/2 ) x->want_primes = 2*x->num_primes;
        else if ( t/2 > pipe->latency && x->num_primes > 1 ) x->want_primes = x->num_primes/2;
        else x->want_primes = x->num_primes;
    } else {
        x->want_primes = x->num_primes;
    }
    if ( ! x->want_primes ) x->want_primes = 1; // ask for 1 prime to start
    sem_post (&pipe->hungry_readers);
    sem_wait (&x->good_to_go);
    if ( x->read_primes >= x->num_primes ) return PRIMES_DONE;
    x->last = get_cycles();
    return x->primes[x->read_primes++];
}

static inline void primes_close_pipe (primes_pipe_ctx_t *pipe, int i)   // readers need to call this when they are done
{
    if ( !pipe->num_readers ) return;
    softassert (i < pipe->num_readers);
    assert (pipe->readers[i].read_primes >= pipe->readers[i].num_primes);   // TODO: allow readers to close pipe early if they wish to?
    assert (!pipe->readers[i].finished);                                    // protect against double close
    pipe->readers[i].finished = 1;
    sem_post(&pipe->finished_readers);
}

static inline int primes_feed_pipe (primes_pipe_ctx_t *pipe)
{
    uint64_t p = 0;
    uint32_t i,j;

    assert (pipe->readers);
    sem_wait (&pipe->hungry_readers);
    if ( ! pipe->ctx ) pipe->ctx = primes_enum_start (pipe->start, pipe->end);
    for ( i = 0 ; i < pipe->num_readers ; i++ ) {
        struct primes_pipe_reader *x = pipe->readers+i;
        if ( x->want_primes > 0 ) {
            for ( j = 0 ; j < x->want_primes && pipe->high < pipe->end && (p = primes_enum_next (pipe->ctx)) <= pipe->end ; j++ ) x->primes[j] = p;
            pipe->high = p;
            x->num_primes = j;  x->read_primes = x->want_primes = 0;
            sem_post(&x->good_to_go);
        }
    }
    if ( pipe->high >= pipe->end ) for ( i = 0 ; i < pipe->num_readers ; i++ ) sem_post(&pipe->readers[i].good_to_go);

    return ( pipe->high < pipe->end );
}

// these are much slower than prime_enum_next/prev
static inline uint64_t primes_next_prime (uint64_t x) { return primesieve_nth_prime(1,x); }
static inline uint64_t primes_prev_prime (uint64_t x) { return primesieve_nth_prime(-1,x); }

static inline uint64_t primes_nth_prime (int64_t n)
    { return ( n <= PRIMES_SMALL_COUNT ? _primes_small_primes[n] : primesieve_nth_prime (n,1) ); }      
static inline uint64_t primes_pi (uint64_t x)
    { return ( x <= PRIMES_SMALL_BOUND ? _primes_small_indexes[x] : primesieve_count_primes (1,x) ); }

// rigorous upper bound on pi(n) based on Shoup p.91 (from Rosser and Schoenfeld)
static inline uint64_t primes_pi_bound (uint64_t n)
{
    double x,y;
    
    if ( n < 59 ) return 18;
    y = log((double)n);
    x = (double) n / y;
    x *= (1.0 + 3.0/(2.0*y));
    return ((uint64_t)ceil(x));
}
 
// rigorous upper bound on the number of powers q <= n of primes p <= m (assumes m <= n but correct in any case)
static inline uint64_t primes_pi_power_bound (uint64_t m, uint64_t n)
{
    uint64_t b,q;
    int e;

    b = 0;
    for ( e = 1, q = n ; m >= 2 ; q = round(pow(n,1.0/++e)) ) {
        if ( m > q ) m = q;
        b += primes_pi_bound(m);
    }
    return b;
}

// quick rough estimate of pi(x) accurate to within 1 percent, takes about 50 cycles
static inline uint64_t primes_pi_rough_estimate (uint64_t x)
{
    if ( x < PRIMES_SMALL_BOUND ) return _primes_small_indexes[x];
    double y = log(x);
    return x/y*(1+1/y+2/(y*y));
}

// Estimate of pi(x) using Li(x) accurate to within O(sqrt(x)), takes about 500 cycles
static inline uint64_t primes_pi_estimate (uint64_t x)
{
    if ( x < PRIMES_SMALL_BOUND ) return _primes_small_indexes[x];
    return logint(x)+0.5;
}

#endif