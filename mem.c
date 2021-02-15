#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <memory.h>
#include <sys/mman.h>

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

static size_t _shared_bytes;
static size_t _shared_allocs;
static size_t _shared_frees;

static size_t _private_bytes;
static size_t _private_allocs;
static size_t _private_frees;

size_t private_bytes (void) { return _private_bytes; }
size_t private_blocks (void) { return _private_allocs - _private_frees; }
size_t shared_bytes (void) { return _shared_bytes; }
size_t shared_blocks (void) { return _shared_allocs - _shared_frees; }

#ifndef MEMLOG
static void mem_printf (const char *format, ...) {}
#else
static void mem_printf (const char *format, ...)
    { va_list args;  va_start(args, format);  vprintf(format, args);  va_end(args); }
#endif


// Use this for memory written by parent to be shared on a readonly basis with forked children (under cygwin we need this to avoid copying in fork)
void *shared_malloc(size_t bytes)
{
    assert (bytes);
    mem_printf ("shared_malloc(%lu)\n", bytes);
    void *ptr = mmap (NULL,bytes,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);  assert (ptr);
    _shared_bytes += bytes;  _shared_allocs++;
    mem_printf ("shared_blocks=%lu, shared_bytes=%lu (%.1f MB)\n", _shared_allocs-_shared_frees, _shared_bytes, (double)_shared_bytes/(1<<20));
    return ptr;
}

void *shared_calloc(size_t bytes)
{
    assert (bytes);
    mem_printf ("shared_calloc(%lu)\n", bytes);
    void *ptr = mmap (NULL,bytes,PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);  assert (ptr);
    memset (ptr,0,bytes);   // don't trust mmap to zero fill
    _shared_bytes += bytes;  _shared_allocs++;
    mem_printf ("shared_blocks=%lu, shared_bytes=%lu (%.1f MB)\n", _shared_allocs-_shared_frees, _shared_bytes, (double)_shared_bytes/(1<<20));
    return ptr;
}

void shared_free (void *ptr, size_t bytes)
{
    assert (bytes);
    mem_printf ("shared_free(%lu)\n", bytes);
    assert (_shared_allocs > _shared_frees && _shared_bytes >= bytes);
    munmap (ptr, bytes);
    _shared_bytes -= bytes; _shared_frees++;
    mem_printf ("shared_blocks=%lu, shared_bytes=%lu (%.1f MB)\n", _shared_allocs-_shared_frees, _shared_bytes, (double)_shared_bytes/(1<<20));
}

// Copies malloced data at oldptr into shared memory, zero extends if needed, frees oldptr, returns pointer to shared copy
// In theory we could use mremap here and avoid the copy but we don't want to rely on cygwin supporting this properly
void *shared_realloc (void *old_ptr, size_t old_bytes, size_t new_bytes)
{
    assert (new_bytes && old_bytes);
    mem_printf ("shared_realloc(%lu -> %lu)\n", old_bytes, new_bytes);
    void *new_ptr = shared_malloc (new_bytes);
    memcpy (new_ptr, old_ptr, old_bytes > new_bytes ? new_bytes : old_bytes);
    if ( new_bytes > old_bytes ) memset ((char *)new_ptr+old_bytes, 0, new_bytes-old_bytes);
    shared_free (old_ptr, old_bytes);
    mem_printf ("shared_blocks=%lu, shared_bytes=%lu (%.1f MB)\n", _shared_allocs-_shared_frees, _shared_bytes, (double)_shared_bytes/(1<<20));
    return new_ptr;
}

// Use this for private unshared memory local to process/thread/child
void *private_malloc (size_t bytes)
{
    assert (bytes);
    mem_printf ("private_malloc(%lu)\n", bytes);
    void *ptr = malloc (bytes);  assert (ptr);
    _private_bytes += bytes;  _private_allocs++;
    mem_printf ("private_blocks=%lu, private_bytes=%lu (%.1f MB)\n", _private_allocs-_private_frees, _private_bytes, (double)_private_bytes/(1<<20));
    return ptr;
}

void *private_calloc (size_t bytes)
{
    assert (bytes);
    mem_printf ("private_calloc(%lu)\n", bytes);
    void *ptr = calloc (1, bytes);  assert (ptr);
    _private_bytes += bytes;  _private_allocs++;
    mem_printf ("private_blocks=%lu, private_bytes=%lu (%.1f MB)\n", _private_allocs-_private_frees, _private_bytes, (double)_private_bytes/(1<<20));
    return ptr;
}

void private_free (void *ptr, size_t bytes)
{
    assert (bytes);
    mem_printf ("private_free(%lu)\n", bytes);
    assert (_private_allocs > _private_frees && _private_bytes >= bytes);
    free (ptr);
    _private_bytes -= bytes; _private_frees++;
    mem_printf ("private_blocks=%lu, private_bytes=%lu (%.1f MB)\n", _private_allocs-_private_frees, _private_bytes, (double)_private_bytes/(1<<20));
}

void *private_realloc (void *old_ptr, size_t old_bytes, size_t new_bytes)
{
    assert (_private_allocs > _private_frees && _private_bytes >= old_bytes);
    mem_printf ("private_realloc(%lu -> %lu)\n", old_bytes, new_bytes);
    void *new_ptr = realloc (old_ptr, new_bytes);  assert (new_ptr);
    if ( new_bytes > old_bytes ) memset ((char *)new_ptr+old_bytes, 0, new_bytes-old_bytes);
    _private_bytes -= old_bytes;
    _private_bytes += new_bytes;
    mem_printf ("private_blocks=%lu, private_bytes=%lu (%.1f MB)\n", _private_allocs-_private_frees, _private_bytes, (double)_private_bytes/(1<<20));
    return new_ptr;
}

void *shared_realloc_private (void *old_private_ptr, size_t old_bytes, size_t new_bytes)
{
    assert (new_bytes && old_bytes);
    mem_printf ("shared_realloc_private(%lu -> %lu)\n", old_bytes, new_bytes);
    void *new_ptr = shared_malloc (new_bytes);
    memcpy (new_ptr, old_private_ptr, old_bytes > new_bytes ? new_bytes : old_bytes);
    if ( new_bytes > old_bytes ) memset ((char *)new_ptr+old_bytes, 0, new_bytes-old_bytes);
    private_free (old_private_ptr, old_bytes);
    mem_printf ("private_blocks=%lu, private_bytes=%lu (%.1f MB)\n", _private_allocs-_private_frees, _private_bytes, (double)_private_bytes/(1<<20));
    mem_printf ("shared_blocks=%lu, shared_bytes=%lu (%.1f MB)\n", _shared_allocs-_shared_frees, _shared_bytes, (double)_shared_bytes/(1<<20));
    return new_ptr;
}

