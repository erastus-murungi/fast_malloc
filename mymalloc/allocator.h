/**
 * Copyright (c) 2020 MIT License by 6.172 Staff
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 **/

/**
 * allocator.h
 *
 * You may include macros, inline helper function definitions, and helper
 * function prototypes here instead of in allocator.c, especially if you like to
 * test them in allocator_test.c.
 **/

#ifndef MM_ALLOCATOR_H
#define MM_ALLOCATOR_H

// All blocks must have a specified minimum alignment.
// The alignment requirement (from config.h) is >= 8 bytes.
#ifndef ALIGNMENT
#define ALIGNMENT 8
#endif

#include <sys/param.h>
#include <stdint.h>
#include <assert.h>
#include <strings.h>
#include <sys/param.h>

#include "validator.h"

// Rounds up to the nearest multiple of ALIGNMENT.
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))

// The smallest aligned size that will hold a size_t value.
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* We use a double linked list to represent our freelist */
typedef struct freelist_t{
    struct freelist_t *prev; /* a pointer to the prev block */
    struct freelist_t *next; /* a pointer to the next block */
} freelist_t;


/* Just an alias to make extracting the sizes easier */
typedef struct size_alias_t {
    uint32_t size;
    uint32_t prev_size;
} size_alias_t;

/* This is the smallest size of any block: composed of two pointers (16 bytes) and 2 unsigned ints (8 bytes) */
#define MINIMUM_BLOCK_SIZE (24)
/* We will be asked for a maximum of 2^32 bytes */
#define MAX_SIZE (32)
/* We will store everything <= 2^5 in one bin */
#define MIN_BIN_SIZE (5)
/* The number of bins that we have. */
#define N_BINS (MAX_SIZE - MIN_BIN_SIZE)
/* If a block is in use then the last bit is a 1 else it is a 0 */
#define IN_USE_MASK (1)

#endif  // MM_ALLOCATOR_H