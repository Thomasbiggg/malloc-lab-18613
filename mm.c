/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Your Name <andrewid@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"
#include <stdint.h> // For uint64_t
/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.
 * Hat tip to Stack Overflow poster chqrlie (see
 * https://stackoverflow.com/questions/72647780).
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__)))
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

/**
 * Mask to ckeck whether previous is allocated or not
 */
static const word_t pre_alloc_mask = 0x2;

/**
 * Mask to check if this free block is a mini block or not =
 */
static const word_t mini_mask = 0x4;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    word_t header;
    union {
        char payload[0]; // Used when the block is allocated to store data.
        struct {
            struct block
                *next; // Pointer to the previous block in the free list.
            struct block *prev; // Pointer to the next block in the free list.
        } address; // Used when the block is free to link free blocks.
    } content;
} block_t;

/* Global variables */
#define SEGSIZE 14
const int tab64[64] = {63, 0,  58, 1,  59, 47, 53, 2,  60, 39, 48, 27, 54,
                       33, 42, 3,  61, 51, 37, 40, 49, 18, 28, 20, 55, 30,
                       34, 11, 43, 14, 22, 4,  62, 57, 46, 52, 38, 26, 32,
                       41, 50, 36, 17, 19, 29, 10, 13, 21, 56, 45, 25, 31,
                       35, 16, 9,  12, 44, 24, 15, 8,  23, 7,  6,  5};
static void delete (block_t *del_block);
static void push(block_t *new_block);
static int log2(size_t value);
static int find_sizeClass(size_t size);
static word_t write_mini(word_t block);
static void update_next_block_bits(block_t *block);
static bool get_prev_mini(block_t *block);
static bool get_pre_alloc(block_t *block);
static bool extract_pre_alloc(word_t word);
static bool extract_mini(word_t word);

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;
static block_t *segregated_lists[SEGSIZE];
static block_t *mini_list = NULL;
// static block_t *head = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */
// https://stackoverflow.com/questions/3064926/how-to-write-log-base2-in-c-c

static int log2(size_t value) {
    value = (uint64_t)value;
    value |= value >> 1;
    value |= value >> 2;
    value |= value >> 4;
    value |= value >> 8;
    value |= value >> 16;
    value |= value >> 32;
    return tab64[((uint64_t)((value - (value >> 1)) * 0x07EDD5E59A4E28C2)) >>
                 58];
}

static int find_sizeClass(size_t size) {
    int size_class = log2(size);

    if (size_class <= 4)
        size_class = 1;
    else if (size_class < 17 && size_class > 4)
        size_class -= 4;
    else if (size_class >= 17)
        size_class = 13;

    return size_class;
}
/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev, bool prev_mini) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (prev) {
        word |= pre_alloc_mask;
    }
    if (prev_mini) {
        word |= mini_mask;
    }
    return word;
}

static word_t pack_bits(word_t addr, bool alloc, bool prev, bool prev_mini) {
    if (alloc) {
        addr |= alloc_mask;
    }
    if (prev) {
        addr |= pre_alloc_mask;
    }
    if (prev_mini) {
        addr |= mini_mask;
    }
    return addr;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, content.payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->content.payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->content.payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

static bool extract_pre_alloc(word_t word) {
    return (bool)(word & pre_alloc_mask);
}

/**
 * @brief Returns the allocation status of its previous block, based on its
 * header.
 * @param[in] block
 * @return The allocation status of the previous block
 */
static bool get_pre_alloc(block_t *block) {
    return extract_pre_alloc(block->header);
}

static bool extract_prev_small(word_t word) {
    return (bool)(word & mini_mask);
}

/**
 * @brief Returns the status of the free block, based on its header.
 * @param[in] block
 * @return The mini status of the block
 */
static bool get_prev_mini(block_t *block) {
    return extract_prev_small(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true, false, false);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc, bool prev,
                        bool prev_mini) {
    dbg_requires(block != NULL);
    // dbg_requires(size > 0);

    block->header = pack(size, alloc, prev, prev_mini);

    // Only free block have footer
    if (size > min_block_size) {
        if (!alloc) {
            word_t *footerp = header_to_footer(block);
            // dbg_printf("Size %ld\n", size);
            *footerp = pack(size, alloc, prev, prev_mini);
        }
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);

    if (get_prev_mini(block)) {
        return (block_t *)((char *)block - dsize);
    }

    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

// update the next_block after split or free or coalesce
static void update_next_block_bits(block_t *block) {
    block_t *next_block = find_next(block);
    if (next_block != NULL) {
        size_t next_next_size = get_size(next_block);
        if (next_next_size != 0 && get_alloc(next_block)) {
            if (get_size(block) == 16) {
                write_block(next_block, next_next_size, true, get_alloc(block),
                            true);
            } else {
                write_block(next_block, next_next_size, true, get_alloc(block),
                            false);
            }
        } else if (next_next_size == 0 && get_alloc(next_block)) {
            if (get_size(block) == 16) {
                write_block(next_block, 0, true, get_alloc(block), true);
            } else {
                write_block(next_block, 0, true, get_alloc(block), false);
            }
        }   
    }
}
/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {
    size_t curSize = get_size(block);

    dbg_requires(block != NULL && "Trying to coalesce nothing");
    dbg_requires(curSize != 0 && "Trying to coalesce prologue or epilogue");

    block_t *prev;
    size_t prevSize = 0;
    bool prevAlloc = get_pre_alloc(block);
    if (!prevAlloc) {
        prev = find_prev(block);
        if (prev != NULL) {
            prevSize = get_size(prev);
        }
    }
    bool prevPro = prevSize == 0;

    block_t *next = find_next(block);
    bool nextAlloc = true;
    size_t nextSize = 0;
    if (next != NULL) {
        nextSize = get_size(next);
        nextAlloc = get_alloc(next);
    }
    bool nextEpi = nextSize == 0; // true if next is epilogue

    // Prev and Next are both not allocated
    if (!prevAlloc && !nextAlloc && !prevPro && !nextEpi) {
        bool prev_alloc = get_pre_alloc(prev);
        bool prev_mini = get_prev_mini(prev);

        delete (prev);
        delete (next);

        curSize += prevSize + nextSize;

        write_block(prev, curSize, false, prev_alloc, prev_mini);

        block = prev;

    }
    // Next is not allocated
    else if (!nextAlloc) {

        delete (next);
        curSize += nextSize;
        write_block(block, curSize, false, prevAlloc, false);

    }
    // Prev is not allocated
    else if (!prevAlloc) {
        bool prev_alloc = get_pre_alloc(prev);
        bool prev_mini = get_prev_mini(prev);

        delete (prev);
        prevSize += curSize;
        write_block(prev, prevSize, false, prev_alloc, prev_mini);

        block = prev;

    } // If both are allocated, no coalescing is done, block remains the same.
    push(block);

    update_next_block_bits(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;
    block_t *brk_res = payload_to_header(mem_sbrk(0));
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    
    write_block(block, size, false, get_pre_alloc(brk_res),
                get_prev_mini(brk_res));
    // The first time extend heap    
    // block_t *prev = NULL;
    // for (prev = heap_start; get_size(block) > 0; block = find_next(block)) {
    //     prev = block;
    // }
    // if (prev) {
    //     if (get_size(prev) == min_block_size) {
    //         if (get_alloc(prev)) {
    //             write_block(block, size, false, true, true);
    //         } else {
    //             write_block(block, size, false, false, true);
    //         }
    //     } else {
    //         if (get_alloc(prev)) {
    //             write_block(block, size, false, true, false);
    //         } else {
    //             write_block(block, size, false, false, false);
    //         }
    //     }
    // } else {
    //     write_block(block, size, false, true, false);
    // }

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // if (segregated_lists[size_class] != NULL)
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */

    size_t block_size = get_size(block);
    size_t splitBlockSize = (block_size - asize);
    if (splitBlockSize >= min_block_size) {

        block_t *block_next;

        write_block(block, asize, true, get_pre_alloc(block),
                    get_prev_mini(block));

        block_next = find_next(block);

        if (asize == min_block_size) {
            write_block(block_next, splitBlockSize, false, true, true);
        } else {
            write_block(block_next, splitBlockSize, false, true, false);
        }

        push(block_next);

        // After splitting, set the allocate bit of next block of split block to
        // false
        update_next_block_bits(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
// static block_t *find_fit(size_t asize) {

//     // Added size classes
//     int size_class = find_sizeClass(asize);

//     // First fit, if no space if found in the size_class. it will go to the
//     next for (int i = size_class; i < 14; i++) {
//         block_t *temp = segregated_lists[i];

//         // Loop through the size_class
//         while (temp != NULL && get_size(temp) > 0) {
//             if (!(get_alloc(temp)) && (asize <= get_size(temp))) {
//                 return temp;
//             }
//             // dbg_printf("heap %p ", (void *)(temp->content.address.next));
//             temp = temp->content.address.next;
//         }

//     }

//     // dbg_printf("\n");
//     return NULL;
// }
static block_t *find_fit(size_t asize) {
    int size_class = find_sizeClass(asize);

    if (asize == min_block_size) {
        block_t *temp = mini_list;
        while (temp != NULL) {
            if (!(get_alloc(temp)) && asize <= get_size(temp)) {
                return temp;
            }
            temp = temp->content.address.next;
        }
    }

    // If couldn't find a place in the minilist, go to seg list
    for (int i = size_class; i < SEGSIZE; i++) {
        block_t *temp = segregated_lists[i];
        block_t *best_fit = NULL;
        // best fit
        while (temp != NULL && get_size(temp) > 0) {
            // dbg_printf("%p -> ", (void *)temp);

            if (!(get_alloc(temp)) && (asize <= get_size(temp))) {
                if (best_fit == NULL || get_size(temp) < get_size(best_fit)) {
                    best_fit = temp;
                    if (get_size(temp) == asize)
                        break; // Perfect fit found, no need to search
                               // further
                }
            }
            temp = temp->content.address.next;
        }
        // dbg_printf("\n");
        if (best_fit != NULL)
            return best_fit;
    }

    return NULL;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    block_t *heap_end = mem_heap_hi();
    block_t *block;
    // int heap_count = 0; // count of free blocks on heap

    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {

        // Check alignment
        if ((size_t)header_to_payload(block) % 16 != 0) {
            dbg_printf("Alignment error %p (called at line %d)\n",
                       (void *)block, line);
            return false;
        }

        // Check heap boundaries
        if (heap_start > block || block > heap_end) {
            dbg_printf("Boundary error (called at line %d)\n", line);
            return false;
        }

        // Check Header and Footer
        size_t size = get_size(block);
        bool alloc = get_alloc(block);
        word_t *footerp = header_to_footer(block);

        if (size > 16 && !alloc) {
            if (alloc != extract_alloc(*footerp) ||
                size != extract_size(*footerp)) {
                dbg_printf("Header or Footer error (called at line %d)\n",
                           line);
                return false;
            }
        }

        // Check if there are two consecutive free blocks
        if (!get_alloc(block)) {
            // heap_count+=1;
            block_t *nextBlock = find_next(block);
            if (nextBlock != NULL && !get_alloc(nextBlock) &&
                get_size(nextBlock) == 0) {
                dbg_printf("consecutive free block error (called at line %d)\n",
                           line);
                return false;
            }
        }
        // dbg_printf("%p %d,%d,%d -> ", (void *)(block), get_alloc(block), get_pre_alloc(block), get_prev_mini(block));
    }

    // // Visualize the heap
    // dbg_printf("Heap \n");
    // int seg_count = 0;
    for (int i = 0; i < SEGSIZE; i++) {
        block_t *temp = segregated_lists[i];
        if (!temp) {
            continue;
        }
        // dbg_printf("list: %d\n", i);
        if (i != 4) {
            while (temp != NULL && get_size(temp) > 0) {
                // seg_count += 1;
                // dbg_printf("%p -> ", (void *)(temp));

                if (find_sizeClass(get_size(temp)) != i) {
                    dbg_printf("block not in right bin size %d)", line);
                    return false;
                }

                if (temp->content.address.prev) {
                    // Check for pointer consistent
                    if (temp->content.address.prev->content.address.next !=
                        temp) {
                        dbg_printf("next/prev pointer not consistent (called "
                                   "at line %d)",
                                   line);
                        return false;
                    }

                    if ((void *)temp->content.address.prev < mem_heap_lo()) {
                        dbg_printf("address lower than prologue (called "
                                   "at line %d)",
                                   line);
                        return false;
                    }

                    if ((void *)temp->content.address.prev > mem_heap_hi()) {
                        dbg_printf("address higher than epilogue (called "
                                   "at line %d)",
                                   line);
                        return false;
                    }
                }

                if (temp->content.address.next) {
                    if (temp->content.address.next->content.address.prev !=
                        temp) {
                        dbg_printf("next/prev pointer not consistent (called "
                                   "at line %d)",
                                   line);
                        return false;
                    }

                    if ((void *)temp->content.address.next < mem_heap_lo()) {
                        dbg_printf("address lower than prologue (called "
                                   "at line %d)",
                                   line);
                        return false;
                    }

                    if ((void *)temp->content.address.next > mem_heap_hi()) {
                        dbg_printf("address higher than epilogue (called "
                                   "at line %d)",
                                   line);
                        return false;
                    }
                }

                temp = temp->content.address.next;
            }
        } else {
            while (temp != NULL && get_size(temp) > 0) {
                // seg_count += 1;

                if (find_sizeClass(get_size(temp)) != 4) {
                    dbg_printf("block not in right bin size %d)", line);
                    return false;
                }

                if (temp->content.address.next) {

                    if ((void *)temp->content.address.next < mem_heap_lo()) {
                        dbg_printf("address lower than prologue (called "
                                   "at line %d)",
                                   line);
                        return false;
                    }

                    if ((void *)temp->content.address.next > mem_heap_hi()) {
                        dbg_printf("address higher than epilogue (called "
                                   "at line %d)",
                                   line);
                        return false;
                    }
                }

                temp = temp->content.address.next;
            }
        }
        // dbg_printf("\n");
    }
    // dbg_printf("\n");
    // if (seg_count != heap_count) {
    //     dbg_printf("free block nums not consistent %d)", line);
    //     return false;
    // }

    // dbg_printf("segregated list free blocks: %d\n", seg_count);
    dbg_requires(segregated_lists[0] == NULL && "sth in seg list");

    // check epilogue
    return true;
}

// LIFO
// https://www.geeksforgeeks.org/introduction-and-insertion-in-a-doubly-linked-list/
static void push(block_t *new_block) {
    dbg_requires(!get_alloc(new_block) && "Pushed allocated block to LL");

    size_t asize = get_size(new_block);
    int size_class = find_sizeClass(asize);

    if (asize > dsize) {
        // block_t *temp = segregated_lists[size_class];
        // dbg_printf("list %d before push \n", size_class);
        // while (temp != NULL && get_size(temp) > 0) {
        //     dbg_printf("%p -> ", (void *)temp);
        //     temp = temp->content.address.next;
        // }
        // dbg_printf("\n");

        // 3. Make next of new node as head and previous as NULL
        new_block->content.address.next = segregated_lists[size_class];
        new_block->content.address.prev = NULL;

        // 4. change prev of head node to new node
        if (segregated_lists[size_class] != NULL)
            segregated_lists[size_class]->content.address.prev = new_block;

        // 5. move the head to point to the new node
        segregated_lists[size_class] = new_block;

        // temp = segregated_lists[size_class];
        // dbg_printf("list %d after push \n", size_class);
        // while (temp != NULL && get_size(temp) > 0) {
        //     dbg_printf("%p -> ", (void *)temp);
        //     temp = temp->content.address.next;
        // }
        // dbg_printf("\n");
    
    } else {
        // 3. Make next of new node as head
        // if (!segregated_lists[size_class]) {
        //     segregated_lists[size_class] = new_block;
        //     new_block->content.address.next = NULL;
        // } else {
        //     new_block->content.address.next = segregated_lists[size_class];
        //     segregated_lists[size_class] = new_block;
        // }

        // block_t *temp = mini_list;
        // dbg_printf("mini list before push \n");
        // while (temp != NULL && get_size(temp) > 0) {
        //     dbg_printf("%p -> ", (void *)temp);
        //     temp = temp->content.address.next;
        // }
        // dbg_printf("\n");

        if (!mini_list) {
            mini_list = new_block;
            new_block->content.address.next = NULL;
        } else {
            new_block->content.address.next = mini_list;
            mini_list = new_block;
        }

        // temp = mini_list;
        // dbg_printf("mini list after push\n");
        // while (temp != NULL && get_size(temp) > 0) {
        //     dbg_printf("%p -> ", (void *)temp);
        //     temp = temp->content.address.next;
        // }
        // dbg_printf("\n");
    }
}

// Delete a node from the doubly linked list
// https://www.geeksforgeeks.org/delete-a-node-in-a-doubly-linked-list/
static void delete (block_t *del_block) {
    // Ensure preconditions are met
    size_t asize = get_size(del_block);
    int size_class = find_sizeClass(asize);

    dbg_requires(del_block != NULL && "Trying to delete a NULL block");
    dbg_requires(!get_alloc(del_block) &&
                 "Trying to delete an allocated block");

    if (asize > dsize) {
        // block_t *temp = segregated_lists[size_class];
        // dbg_printf("list %d before delete \n", size_class);
        // while (temp != NULL && get_size(temp) > 0) {
        //     dbg_printf("%p -> ", (void *)temp);
        //     temp = temp->content.address.next;
        // }
        // dbg_printf("\n");

        /* If node to be deleted is head node */
        if (segregated_lists[size_class] == del_block) {
            segregated_lists[size_class] = del_block->content.address.next;
        }

        /* Change next only if node to be deleted is NOT the first node */
        if (del_block->content.address.prev != NULL) {
            del_block->content.address.prev->content.address.next =
                del_block->content.address.next;
        }

        /* Change next only if node to be deleted is NOT the last node */
        if (del_block->content.address.next != NULL) {
            del_block->content.address.next->content.address.prev =
                del_block->content.address.prev;
        }

        // Clear del_block's pointers to avoid dangling references
        del_block->content.address.prev = NULL;
        del_block->content.address.next = NULL;

        // temp = segregated_lists[size_class];
        // dbg_printf("list %d  after delete \n", size_class);
        // while (temp != NULL && get_size(temp) > 0) {
        //     dbg_printf("%p -> ", (void *)temp);
        //     temp = temp->content.address.next;
        // }
        // dbg_printf("\n");

    } else {
        // Mini block (block->header = prev, block->content.address.prev = next)
        // block_t *nextBlock = del_block->content.address.next;

        // if (segregated_lists[size_class] == del_block) {
        //     if (nextBlock != NULL) {
        //         segregated_lists[size_class] = nextBlock;
        //     } else {
        //         segregated_lists[size_class] = NULL;
        //     }
        // } else {
        //     block_t *temp = segregated_lists[size_class];
        //     while (temp->content.address.next != del_block) {
        //         temp = temp->content.address.next;
        //     }
        //     temp->content.address.next = del_block->content.address.next;
        // }

        // del_block->content.address.next = NULL;

        // block_t *temp = mini_list;
        // dbg_printf("mini list before delete\n");
        // while (temp != NULL && get_size(temp) > 0) {
        //     dbg_printf("%p -> ", (void *)temp);
        //     temp = temp->content.address.next;
        // }
        // dbg_printf("\n");


        if (mini_list == del_block) {
            if (!(mini_list->content.address.next)) {
                mini_list = NULL;
            } else {
                mini_list = del_block->content.address.next;
            }
        } else {
            block_t *temp = mini_list;
            while (temp->content.address.next != del_block) {
                temp = temp->content.address.next;
            }
            temp->content.address.next = del_block->content.address.next;
        }
        del_block->content.address.next = NULL;

        // temp = mini_list;
        // dbg_printf("mini list after delete\n");
        // while (temp != NULL && get_size(temp) > 0) {
        //     dbg_printf("%p -> ", (void *)temp);
        //     temp = temp->content.address.next;
        // }
        // dbg_printf("\n");
    }

}
/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about why we need a heap prologue and epilogue. Why do
     * they correspond to a block footer and header respectively?
     */

    start[0] = pack(0, true, false, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Reset the explicit head whenever called init
    for (int i = 0; i < SEGSIZE; i++) {
        segregated_lists[i] = NULL;
    }

    mini_list = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);

    // Couldn't find a place to allocate, so it may need to coalesce after
    // extend need to check whether the seg list is NULL, can not delete from a
    delete(block);

    write_block(block, block_size, true, get_pre_alloc(block),
                get_prev_mini(block));

    // Try to split the block if too large
    split_block(block, asize);

    if (get_alloc(find_next(block)))
        update_next_block_bits(block);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free, first set the pre_alloc to true, if the prev if
    // free, modify it on coalesce_block
    write_block(block, size, false, get_pre_alloc(block), get_prev_mini(block));

    // Try to coalesce the block with its neighbors
    coalesce_block(block);

    // The current block will be freed, so set the pre_alloc of the next block
    // to false update_next_block_bits(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */

