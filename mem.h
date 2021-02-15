#ifndef _MEM_INCLUDE_
#define _MEM_INCLUDE_

/*
    Copyright (c) 2019-2020 Andrew R. Booker and Andrew V. Sutherland
    See LICENSE file for license details.
*/

/*
    Memory management functions supporting memory sharing across forked child processes.  Also used to track memory usage.
    No synchronization is provided, this is up to the caller.

    Our main use case is on cygwin (where local memory gets copied on fork rather than marked as copy on write).
    Parent can create shared memory and all fork children will then have access to it (without needing to do anything)
*/

// Use these functions for child specific memory
void *private_malloc (size_t bytes);
void *private_calloc (size_t bytes);
void *private_realloc (void *oldptr, size_t bytes);
void private_free (void *ptr, size_t bytes);

// Use these function for memory written by parent to be shared on a readonly basis with forked children (under cygwin we need this to avoid copying in fork)
void *shared_malloc (size_t bytes);
void *shared_calloc (size_t bytes);
void *shared_realloc (void *old_ptr, size_t old_bytes, size_t new_bytes);
void *shared_realloc_private (void *old_private_ptr, size_t old_bytes, size_t new_bytes);
void shared_free (void *ptr, size_t bytes);

size_t private_bytes (void);
size_t private_blocks (void);
size_t shared_bytes (void);
size_t shared_blocks (void);

#endif
