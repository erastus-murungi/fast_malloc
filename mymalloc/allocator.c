/**
 * Copyright (c) 2015 MIT License by 6.172 Staff
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

#include "./allocator.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "./allocator_interface.h"
#include "./memlib.h"

// Don't call libc malloc!
#define malloc(...) (USE_MY_MALLOC)
#define free(...) (USE_MY_FREE)
#define realloc(...) (USE_MY_REALLOC)

void* used_end;

/* returns a pointer header of `ptr`*/
static inline size_alias_t* get_size_alias_pointer(void* ptr) {
  assert(ptr != NULL);
  return ((size_alias_t*)((uint64_t)ptr - SIZE_T_SIZE));
}

static inline uint32_t get_size(void* ptr) {
  assert(ptr != NULL);
  return get_size_alias_pointer(ptr)->size;
}

static inline uint32_t get_prev_size(void* ptr) {
  assert(ptr != NULL);
  return get_size_alias_pointer(ptr)->prev_size &
         ~1ULL; /* the last bit carries information we do not want */
}

static inline void set_size(void* ptr, uint32_t aligned_size) {
  assert(IS_ALIGNED(aligned_size));
  assert(ptr != NULL);

  get_size_alias_pointer(ptr)->size = aligned_size;
}

static inline void update_used_end_size() {
  *(uint32_t*)(used_end - SIZE_T_SIZE) =
      mem_heap_hi() + 1 - used_end - SIZE_T_SIZE;
}

/**
 * @brief Finds the freelist where memory block of size `size` resides
 *
 * @param size the number of bytes to be allocated
 *
 * Note that all memory sizes of size 2^0 ... 2^MIN_BIN_SIZE go to one bin
 */
static int32_t find_bin_index(uint32_t size) {
  return MAX(0, MAX_SIZE - MIN_BIN_SIZE - __builtin_clz(size));
}

static inline void set_bit(uint32_t* w, uint8_t position, uint8_t value) {
  *w = (*w & ~(1UL << position)) | (value << position);
}

static inline int is_set(uint32_t w, uint8_t position) {
  return (w >> position) & 1;
}

static inline bool is_lsb_set(uint32_t w) { return is_set(w, 0); }

/**
 * @brief       A helper function which checks whether the block at the `ptr`
 * previous block is in use.
 */
static inline bool prev_block_in_use(void* ptr) {
  assert(ptr != NULL);
  return is_lsb_set(get_size_alias_pointer(ptr)->prev_size);
}

/**
 * @brief       A helper function to check whether the block following the one
 * provided is in use
 *
 * @param ptr   a pointer to the beginning of the freelist (doesn't include the
 * size header)
 * @return      true if the freelist at `ptr` is being used and false otherwise
 *
 * Assumes that the next two blocks after the one starting at `ptr` do
 * not extend the heap
 */
static inline bool next_block_in_use(void* ptr) {
  assert(ptr != NULL);
  const uint32_t plus_header_size = get_size(ptr) + SIZE_T_SIZE;
  const uint32_t next_plus_header_size =
      get_size(ptr + plus_header_size) + SIZE_T_SIZE;
  return prev_block_in_use(ptr + plus_header_size + next_plus_header_size);
}

/**
 * @brief          A helper function to mark that some freelist is in use
 *
 * @param ptr      A pointer to a freelist
 * @param in_use  `true` if the freelist at `ptr` is being used and false
 * otherwise
 */
static inline void set_in_use(void* ptr, bool in_use) {
  const int32_t next_block_offset = get_size(ptr);
  assert(ptr != NULL);
  if (in_use) {
    get_size_alias_pointer(ptr + next_block_offset + SIZE_T_SIZE)->prev_size =
        next_block_offset | IN_USE_MASK;
  } else {
    get_size_alias_pointer(ptr + next_block_offset + SIZE_T_SIZE)->prev_size =
        next_block_offset & ~IN_USE_MASK;
  }
}

/**
 * @brief Attempts to find the index of a bin whose block sizes are larger than
 * 2^(i+1)
 *
 * It is acceptable to return 0 when no bigger freelists are available because
 * 0 can never be returned by this function -- this would imply we called this
 * function with i < 0;
 *
 * @param w   the bitmask who's i'th bit is set if bins[i] != NULL
 * @param i   an index telling us we should find a free bin in the range
 * w[i+1:31]
 *
 * @return    an `index` such than (bins[`index`] != NULL and `index` > i)
 *            or 0 if no such index is found
 */
static inline int32_t find_index_of_next_free_bin(uint32_t w, int32_t i) {
  const int32_t j = (i + 1);
  const uint32_t c = w >> j;
  return (c) ? __builtin_ctz(c) + j : 0;
}

// check - This checks our invariant that the size_t header before every
// block points to either the beginning of the next block, or the end of the
// heap.
int my_check() {
  char* p;
  char* lo = (char*)mem_heap_lo();
  char* hi = (char*)mem_heap_hi() + 1;
  size_t size = 0;

  p = lo + SIZE_T_SIZE; /* we allocated a header in my_init_*/
  while (lo <= p && p < hi) {
    size = ALIGN(get_size(p) + SIZE_T_SIZE);
    p += size;
  }

  if (p != hi) {
    printf("diff: %ld\n", hi - p);
    printf("Bad headers did not end at heap_hi!\n");
    printf("heap_lo: %p, heap_hi: %p, size: %lu, p: %p\n", lo, hi, size, p);
    return -1;
  }

  return 0;
}

freelist_t* bins[N_BINS];

/* This is a bitmask whose i'th bit is set iff bins[i] != NULL.
 * It is useful when searching for a next larger non-empty bin
 */
static uint32_t is_full;

// init - Initialize the malloc package.  Called once before any other
// calls are made.  Since this is a very simple implementation, we just
// return success.
int my_init() {
  /* it is possible that our heap is not aligned*/
  size_t hi = (size_t)mem_heap_hi() + 1;
  unsigned int extra_size = ALIGN(hi) - hi;
  mem_sbrk(extra_size);

  /* We look at the first header, and set that it's in use and
   * that it's size is 0 */
  size_alias_t* size_alias = (size_alias_t*)mem_sbrk(SIZE_T_SIZE);
  size_alias->size = 0;
  /* we don't have a previous block so it's LSB(prev_size) must be equal to 0 */
  size_alias->prev_size = IN_USE_MASK;

  for (int i = 0; i < N_BINS; i++) {
    bins[i] = NULL;
  }
  is_full = 0;
  used_end = (void*)((char*)mem_heap_hi() + 1);
  update_used_end_size();

  return 0;
}

/**
 * @brief            Checks if the current block fits in the free space before
 *                   the end of the heap. If the block doesn't fit, extends the
 * heap only by the needed amount.
 *
 * @param total_size the size of the block to be allocated
 * @return           a pointer to the allocated block
 */
static inline void* extend_heap(uint32_t total_size) {
  void* heap_hi = (void*)((char*)mem_heap_hi() + 1);
  uint64_t remaining_space = (uint64_t)heap_hi - (uint64_t)used_end;
  if (total_size > remaining_space) {
    void* new_ptr = used_end;
    assert(ALIGNED(total_size - remaining_space));
    mem_sbrk(total_size - remaining_space);
    used_end = (void*)((char*)mem_heap_hi() + 1);
    update_used_end_size();
    assert(ALIGNED(new_ptr));
    return new_ptr;
  } else {
    void* new_ptr = used_end;
    assert(ALIGNED(new_ptr));
    used_end = (void*)((char*)used_end + total_size);
    update_used_end_size();
    return new_ptr;
  }
}

/**
 * @brief             Removes a freelist `freelist` from bins[`bin_index`].
 *
 * Assumes that freelist is in bins[`bin_index`]
 *
 * @param freelist    the freelist to remove
 * @param bin_index   the index in the bins of where `freelist` is
 */
void remove_block_from_free_list(freelist_t* freelist, uint32_t bin_index) {
  freelist_t* next = freelist->next;
  freelist_t* prev = freelist->prev;
  if (next != NULL) {
    next->prev = prev;
  }
  if (prev != NULL) {
    prev->next = next;
  } else {
    bins[bin_index] = next;
    set_bit(&is_full, bin_index, (bins[bin_index] != NULL));
    assert(((bins[bin_index] != NULL) == is_set(is_full, bin_index)));
  }
}

/**
 * @brief        Checks whether the block starting at ptr goes below the heap
 *
 * @param ptr    a pointer to the beginning of the memory block
 * @return true  the memory block is below the heap
 * @return false the memory block is above the heap
 */
static inline bool is_below_heap_hi(void* ptr) {
  return (ptr + get_size(ptr) + SIZE_T_SIZE) < my_heap_hi();
}

/**
 * @brief        Checks whether the block starting at ptr goes above the heap
 *
 * @param ptr    a pointer to the beginning of the memory block
 * @return true  the memory block is above the heap
 * @return false the memory block is below the heap
 */
static inline bool is_above_heap_lo(void* ptr) {
  return ptr - SIZE_T_SIZE > my_heap_lo();
}

/**
 * @brief split the current block, and return a block_size of exactly
 * requested_size
 *
 * After splitting, the rest of the freelist is put in its corresponding
 * freelist
 *
 * @param freelist        the freelist to split
 * @param requested_size  the number of total bytes requested: header inclusive
 * @return                a pointer to the block of the requested_size to be
 * allocated
 */

freelist_t* split_free_list(freelist_t* freelist, uint32_t requested_size) {
  assert(IS_ALIGNED(requested_size) && requested_size >= MINIMUM_BLOCK_SIZE);
  assert(freelist != NULL);

  int32_t total_size = get_size(freelist) + SIZE_T_SIZE;
  assert(total_size >= requested_size + MINIMUM_BLOCK_SIZE);

  int32_t remaining_size = total_size - requested_size;
  assert(remaining_size >= MINIMUM_BLOCK_SIZE);

  freelist_t* remaining_freelist;
  freelist_t* allocated_freelist;

  if (is_below_heap_hi((void*)freelist) && next_block_in_use((void*)freelist) &&
      get_size((char*)freelist + total_size) == requested_size - SIZE_T_SIZE) {
    allocated_freelist = (freelist_t*)((char*)freelist + remaining_size);
    remaining_freelist = freelist;
  } else {
    allocated_freelist = freelist;
    remaining_freelist = (freelist_t*)((char*)freelist + requested_size);
  }

  int32_t remaining_bin_index = find_bin_index(remaining_size);
  freelist_t* remaining_bin_head = bins[remaining_bin_index];

  set_size(remaining_freelist, remaining_size - SIZE_T_SIZE);
  set_in_use(remaining_freelist, false);
  set_size(allocated_freelist, requested_size - SIZE_T_SIZE);
  set_in_use(allocated_freelist, false);

  // inserting a node into the beginning of a doubly linked list:
  // https://codeforwin.org/2015/10/c-program-to-insert-node-in-doubly-linked-list.html
  remaining_freelist->prev = NULL;
  remaining_freelist->next = remaining_bin_head;

  if (remaining_bin_head != NULL) {
    remaining_bin_head->prev = remaining_freelist;
  }
  bins[remaining_bin_index] = remaining_freelist;
  assert(bins[remaining_bin_index] != NULL);
  set_bit(&is_full, remaining_bin_index, 1);
  return allocated_freelist;
}

/**
 * @brief Attempts to allocate total_requested_size bytes of memory from a free
 * list
 *
 * @param total_requested_size The total number of bytes to be allocated.
 * @return                      a pointer to the allocated memory or NULL if no
 * such memory could be allocated from a free list
 *
 * requires total_requested_size to be the total requested #bytes. This includes
 * the header space. requires total_requested_size to be aligned
 */
static void* malloc_from_binned_free_list(size_t total_requested_size) {
  assert(total_requested_size >= MINIMUM_BLOCK_SIZE &&
         IS_ALIGNED(total_requested_size));

  const int32_t bin_index = find_bin_index(total_requested_size);
  freelist_t* freelist = bins[bin_index];
  int aligned_size = total_requested_size - SIZE_T_SIZE;

  /* we try to find an appropriate freelist in the right bin*/
  while (freelist != NULL) {
    /* we want the total of size of the freelist we are currently looking at*/
    int freelist_total_size = get_size(freelist) + SIZE_T_SIZE;
    if (freelist_total_size >= total_requested_size) {
      /* this is the node we want, we remove it from its correspoding bin */
      remove_block_from_free_list(freelist, bin_index);
      if (freelist_total_size - total_requested_size >= MINIMUM_BLOCK_SIZE) {
        /* If splitting is possible
         * TODO: see whether increasing MINIMUM_BLOCK_SIZE improves
         * performance*/
        freelist = split_free_list(freelist, total_requested_size);
      } else {
        aligned_size =
            freelist_total_size - SIZE_T_SIZE; /* re-adjust the size */
      }
      set_in_use(freelist, true);
      set_size(freelist, aligned_size);
      return (void*)freelist;
    }
    freelist = freelist->next;
  }
  /* we couldn't find any so we move on to higher bins */
  const int32_t larger_bin_index =
      find_index_of_next_free_bin(is_full, bin_index);
  if (larger_bin_index != 0) {
    assert(larger_bin_index > bin_index);

    freelist = bins[larger_bin_index];
    assert(freelist != NULL);

    remove_block_from_free_list(freelist, larger_bin_index);

    const int32_t freelist_total_size = get_size(freelist) + SIZE_T_SIZE;
    if (freelist_total_size - total_requested_size >= MINIMUM_BLOCK_SIZE) {
      freelist = split_free_list(freelist, total_requested_size);
    } else {
      aligned_size = freelist_total_size - SIZE_T_SIZE;
    }
    set_size(freelist, aligned_size);  // re-adjust the size
    set_in_use(freelist, true);
    return (void*)freelist;
  }
  return NULL;
}

//  malloc - Allocate a block by incrementing the brk pointer.
//  Always allocate a block whose size is a multiple of the alignment.
void* my_malloc(size_t size) {
  // We allocate a little bit of extra memory so that we can store the
  // size of the block we've allocated.  Take a look at realloc to see
  // one example of a place where this can come in handy.
  if (size == 0) {
    return NULL;
  }
  int32_t aligned_size = ALIGN(size);
  uint32_t aligned_total_size = ALIGN(size + SIZE_T_SIZE);

  if (aligned_total_size <= MINIMUM_BLOCK_SIZE) {
    aligned_size = MINIMUM_BLOCK_SIZE - SIZE_T_SIZE;  // 16 bytes
    aligned_total_size = MINIMUM_BLOCK_SIZE;          // 24 bytes
  }

  void* p = malloc_from_binned_free_list(aligned_total_size);
  if (p != NULL) {
    return p;
  }

  // Expands the heap by the given number of bytes and returns a pointer to
  // the newly-allocated area.  This is a slow call, so you will want to
  // make sure you don't wind up calling it on every malloc.
  // p = mem_sbrk(aligned_total_size);
  p = extend_heap(aligned_total_size);

  if (p == (void*)-1) {
    // Whoops, an error of some sort occurred.  We return NULL to let
    // the client code know that we weren't able to allocate memory.
    return NULL;
  } else {
    // We store the size of the block we've allocated in the first
    // SIZE_T_SIZE bytes.
    set_size(p, aligned_size);
    set_in_use(p, true);

    // Then, we return a pointer to the rest of the block of memory,
    // which is at least size bytes long.  We have to cast to uint8_t
    // before we try any pointer arithmetic because voids have no size
    // and so the compiler doesn't know how far to move the pointer.
    // Since a uint8_t is always one byte, adding SIZE_T_SIZE after
    // casting advances the pointer by SIZE_T_SIZE bytes.
    return (void*)p;
  }
}

/**
 * @brief                 A helper function which coalesces one freelist block
 * to its next one in memory.
 *
 * @param freelist_self   A freelist.
 *                        It is assumed that freelist_self->next != NULL and is
 * not in use
 */
static inline void coalesce_with_next(void* freelist_self) {
  assert(freelist_self != NULL);
  const int32_t self_size = get_size(freelist_self);

  freelist_t* freelist_next =
      (freelist_t*)((uint64_t)freelist_self + self_size + SIZE_T_SIZE);
  assert(freelist_next != NULL);
  assert(!is_lsb_set(
      get_prev_size(freelist_next)));  // check that self->next is not in use

  const int32_t next_size = get_size(freelist_next);
  remove_block_from_free_list(freelist_next,
                              find_bin_index(next_size + SIZE_T_SIZE));
  set_size(freelist_self, self_size + SIZE_T_SIZE + next_size);
}

/**
 * @brief                 A helper function which coalesces one freelist block
 * with its previous one in memory.
 *
 * @param freelist_self   A freelist.
 *                        It is assumed that freelist_self->prev != NULL and is
 * not in use
 * @return                A pointer to the beginning of the new coalesced
 * freelist block
 */
static inline void* coalesce_with_prev(void* freelist_self) {
  assert(freelist_self != NULL);
  assert(!is_lsb_set(
      get_prev_size(freelist_self)));  // check that prev is not in use

  const int32_t self_size = get_size(freelist_self);
  const int32_t prev_size = get_prev_size(freelist_self);

  freelist_t* freelist_prev = freelist_self =
      (char*)freelist_self - prev_size - SIZE_T_SIZE;
  assert(freelist_prev != NULL);

  remove_block_from_free_list((freelist_t*)freelist_self,
                              find_bin_index(prev_size + SIZE_T_SIZE));
  set_size(freelist_prev, self_size + prev_size + SIZE_T_SIZE);
  // we are modifying pointers here
  return freelist_prev;
}

/**
 * @brief       Attempts to coalesce the freelist_t block `ptr` with its
 * neighbors
 *
 * @param ptr   A pointer to attempt coalescing
 * @returns     A pointer to the beginning of a possible new coalesced block
 */
static inline void* coalesce(void* ptr, bool skip_next) {
  if (!skip_next && is_below_heap_hi(ptr) && !next_block_in_use(ptr)) {
    coalesce_with_next(ptr);
  }
  if (is_above_heap_lo(ptr) && !prev_block_in_use(ptr)) {
    ptr = coalesce_with_prev(ptr);
  }
  return ptr;
}

/**
 * frees the memory pointed to by `ptr`
 */

void my_free(void* ptr) {
  if (ptr == NULL) return;
  bool skip_next = false;
  void* block_end = (void*)((char*)ptr + get_size(ptr) + SIZE_T_SIZE);
  if (block_end == used_end) {
    // don't coalesce the used_end block
    skip_next = true;
  }
  ptr = coalesce(ptr, skip_next);
  set_in_use(ptr, false);
  void* free_block_end = (void*)((char*)ptr + get_size(ptr) + SIZE_T_SIZE);
  assert(used_end - SIZE_T_SIZE >= mem_heap_lo());
  if (free_block_end == (void*)((char*)used_end)) {
    used_end = ptr;
    update_used_end_size();
    return;
  }
  // set_in_use(ptr, false);
  int32_t total_size = get_size(ptr) + SIZE_T_SIZE;
  assert(IS_ALIGNED(total_size) && total_size >= MINIMUM_BLOCK_SIZE);
  int32_t bin_index = find_bin_index(total_size);

  freelist_t* freelist = ptr;
  freelist->next = NULL;
  freelist->prev = NULL;

  freelist_t* freelist_head = bins[bin_index];
  if (freelist_head == NULL) {
    bins[bin_index] = freelist;
  } else {
    freelist_head->prev = freelist;
    freelist->next = freelist_head;
    bins[bin_index] = freelist;
  }
  assert(bins[bin_index] != NULL);
  set_bit(&is_full, bin_index, 1);
}

// realloc - reallocates a space of size size, and copies the minimum of
// get_size(ptr) and size amounts
// of memory from ptr to the new space
void* my_realloc(void* ptr, size_t new_size) {
  if (ptr == NULL) {
    return my_malloc(new_size);
  }
  if (new_size == 0) {
    my_free(ptr);
    return ptr;
  }
  new_size = ALIGN(new_size);
  int32_t size = get_size(ptr);
  int32_t plus_header_size = size + SIZE_T_SIZE;

  /* first optimization: if new_size is larger than previous_size,
    then shrink the current block put the remainder block into the free
    lists */
  if (size >= new_size) {
    int remaining_size = size - new_size;
    if ((char*)ptr + size + SIZE_T_SIZE == used_end) {
      used_end = (char*)ptr + new_size + SIZE_T_SIZE;
      update_used_end_size();
      set_size(ptr, new_size);
      return ptr;
    }
    if (remaining_size >= MINIMUM_BLOCK_SIZE) {
      ptr = (void*)split_free_list((freelist_t*)ptr, plus_header_size);
    }
    return ptr;
  }

  const size_t copy_size = get_size(ptr);

  /* second optimization: if this block reaches the exact end of the heap,
   just extend the heap by the (new_size - size) */
  if (ptr + plus_header_size == my_heap_hi() + 1) {
    mem_sbrk(new_size - size);
    set_size(ptr, new_size);
    set_in_use(ptr, true);
    used_end = my_heap_hi() + 1;
    update_used_end_size();
    return ptr;
  }

  // Allocate a new chunk of memory, and fail if that allocation fails.
  void* newptr = my_malloc(new_size);
  if (NULL == newptr) {
    return NULL;
  }

  // This is a standard library call that performs a simple memory copy.
  memcpy(newptr, ptr, copy_size);

  // Release the old block.
  my_free(ptr);

  // Return a pointer to the new block.
  return newptr;
}