/* 
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first fit placement, and boundary tag coalescing, as described
 * in the CS:APP2e text. Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. 
 *
 * This version is loosely based on 
 * http://csapp.cs.cmu.edu/public/ics2/code/vm/malloc/mm.c
 * but unlike the book's version, it does not use C preprocessor 
 * macros or explicit bit operations.
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <assert.h>
#include "list.h"
#include "tree.h"

#include "mm.h"
#include "memlib.h"

#include "mm_ts.c"

struct boundary_tag {
    int inuse:1;        // inuse bit
    int size:31;        // size of block, in words
};

/* FENCE is used for heap prologue/epilogue. */
const struct boundary_tag FENCE = { .inuse = 1, .size = 0 };

/* A C struct describing the beginning of each block. 
 * For implicit lists, used and free blocks have the same 
 * structure, so one struct will suffice for this example.
 * If each block is aligned at 4 mod 8, each payload will
 * be aligned at 0 mod 8.
 */
struct block {
    struct boundary_tag header; /* offset 0, at address 4 mod 8 */
    union {                 /* offset 4, at address 0 mod 8 */
        char payload[0];
        RB_ENTRY(block) node;
    };
};


/*Compares elements a to b. Returns -1 if smaller and 1 if bigger
  0 is never returned as ties are broken by their address. Better implementations might
  put duplicate sized blocks into a linked list */
static int compare_size(struct block * a, struct block * b)
{
    if (a->header.size < b->header.size)
    {
        return -1;
    }
    else if (a->header.size > b->header.size)
    {
        return 1;
    }
    else
    {
        if(a < b)
        {
            return -1;
        }
        else if(a > b)
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }
    
}

RB_HEAD(mytree, block) tree;

RB_GENERATE_STATIC(mytree, block, node, compare_size); 



/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define MIN_BLOCK_SIZE_WORDS 8 /* Minimum block size in words */
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (words) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Global variables */
static struct block *heap_listp = 0;  /* Pointer to first block */  
static struct boundary_tag * initial;

/* Function prototypes for internal helper routines */
static struct block *extend_heap(size_t words);
static void place(struct block *bp, size_t asize, int mode);
static struct block *find_fit(size_t asize);
static struct block *coalesce(struct block *bp);

/* Given a block, obtain previous's block footer.
   Works for left-most block also. */
static struct boundary_tag * prev_blk_footer(struct block *blk) {
    return &blk->header - 1;
}

/* Return if block is free */
static bool blk_free(struct block *blk) { 
    return !blk->header.inuse; 
}

/* Return size of block is free */
static size_t blk_size(struct block *blk) { 
    return blk->header.size; 
}

/* Given a block, obtain pointer to previous block.
   Not meaningful for left-most block. */
static struct block *prev_blk(struct block *blk) {
    struct boundary_tag *prevfooter = prev_blk_footer(blk);
    assert(prevfooter->size != 0);
    return (struct block *)((size_t *)blk - prevfooter->size);
}

/* Given a block, obtain pointer to next block.
   Not meaningful for right-most block. */
static struct block *next_blk(struct block *blk) {
    assert(blk_size(blk) != 0);
    return (struct block *)((size_t *)blk + blk->header.size);
}

/* Given a block, obtain its footer boundary tag */
static struct boundary_tag * get_footer(struct block *blk) {
    return (void *)((size_t *)blk + blk->header.size) 
                   - sizeof(struct boundary_tag);
}

/* Set a block's size and inuse bit in header and footer */
static void set_header_and_footer(struct block *blk, int size, int inuse) {
    blk->header.inuse = inuse;
    blk->header.size = size;
    * get_footer(blk) = blk->header;    /* Copy header to footer */
}

/* Mark a block as used and set its size. */
static void mark_block_used(struct block *blk, int size) {
    set_header_and_footer(blk, size, 1);
}

/* Mark a block as free and set its size. */
static void mark_block_free(struct block *blk, int size) {
    set_header_and_footer(blk, size, 0);
}

/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    initial = mem_sbrk(2 * sizeof(struct boundary_tag));

    if (initial == (void *)-1)
        return -1;

    RB_INIT(&tree);

    /* We use a slightly different strategy than suggested in the book.
     * Rather than placing a min-sized prologue block at the beginning
     * of the heap, we simply place two fences.
     * The consequence is that coalesce() must call prev_blk_footer()
     * and not prev_blk() - prev_blk() cannot be called on the left-most
     * block.
     */
    initial[0] = FENCE;                     /* Prologue footer */
    heap_listp = (struct block *)&initial[1];
    //RB_INSERT(mytree, &tree, heap_listp);

    /**
    struct element* e = (struct element *)&initial[2];;
    e->size = blk_size(heap_listp);
    list_init(&e->duplication);
    list_push_back(&e->duplication, &heap_listp->elem);
    RB_INSERT(mytree, &tree, e);
    **/

    initial[1] = FENCE;                     /* Epilogue header */


    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL) 
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc(size_t size)
{
    size_t awords;      /* Adjusted block size in words */
    size_t extendwords;  /* Amount to extend heap if no fit */
    struct block *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size += 2 * sizeof(struct boundary_tag);    /* account for tags */
    size = (size + DSIZE - 1) & ~(DSIZE - 1);   /* align to double word */
    awords = MAX(MIN_BLOCK_SIZE_WORDS, size/WSIZE);
                                                /* respect minimum size */

    /* Search the free list for a fit */
    if ((bp = find_fit(awords)) != NULL) {
        place(bp, awords,0);
        return bp->payload;
    }

    /* No fit found. Get more memory and place the block */
    extendwords = MAX(awords,CHUNKSIZE);
    if ((bp = extend_heap(extendwords)) == NULL)  
        return NULL;
    place(bp, awords,1);
    return bp->payload;
} 

/* 
 * mm_free - Free a block 
 */
void mm_free(void *bp)
{
    if (bp == 0) 
        return;

    /* Find block from user pointer */
    struct block *blk = bp - offsetof(struct block, payload);
    if (heap_listp == 0) {
        mm_init();
    }

    mark_block_free(blk, blk_size(blk));
    coalesce(blk);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static struct block *coalesce(struct block *bp) 
{
    //printf("This is coalesce");
    bool prev_alloc = prev_blk_footer(bp)->inuse;
    bool next_alloc = ! blk_free(next_blk(bp));
    size_t size = blk_size(bp);

    if (prev_alloc && next_alloc) {            /* Case 1 */
        
        RB_INSERT(mytree, &tree, bp);

        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */

        struct block* next = next_blk(bp);
        RB_REMOVE(mytree, &tree, next);
        mark_block_free(bp, size + blk_size(next_blk(bp)));
        RB_INSERT(mytree, &tree, bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        //printf("wrong here");
        struct block* prev = prev_blk(bp);
        RB_REMOVE(mytree, &tree, prev);

        bp = prev_blk(bp);
        mark_block_free(bp, size + blk_size(bp));
        RB_INSERT(mytree, &tree, bp);
    }

    else {                                     /* Case 4 */
        struct block* prev = prev_blk(bp);
        RB_REMOVE(mytree, &tree, prev);

        struct block* next = next_blk(bp);
        RB_REMOVE(mytree, &tree, next);

        mark_block_free(prev_blk(bp), 
                        size + blk_size(next_blk(bp)) + blk_size(prev_blk(bp)));
        bp = prev_blk(bp);
        RB_INSERT(mytree, &tree, bp);
    }

    return bp;
}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;
    //struct block * temp = (struct block *)ptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        printf("ptr is NULL" );  
        return mm_malloc(size);
    }

    size += 2 * sizeof(struct boundary_tag);    /* account for tags */
    size = (size + DSIZE - 1) & ~(DSIZE - 1);   /* align to double word */
    size_t awords = MAX(MIN_BLOCK_SIZE_WORDS, size/WSIZE);

    struct block *oldblock = ptr - offsetof(struct block, payload);

    if(blk_free(next_blk(oldblock)))
    {
        struct block *nextBlock = next_blk(oldblock);
        size_t newSize = blk_size(oldblock) + blk_size(nextBlock);
        if(newSize >= awords)
        {
            RB_REMOVE(mytree, &tree, nextBlock);

            if ((newSize - awords) >= MIN_BLOCK_SIZE_WORDS) 
            { 
                mark_block_used(oldblock, awords);
                struct block * nxtBlock = next_blk(oldblock);
                mark_block_free(nxtBlock, newSize - awords);
                RB_INSERT(mytree, &tree, nxtBlock);
            }
            return oldblock->payload;
        }
        
    }      

    newptr = mm_malloc(size);
    if(!newptr) 
    {
        return 0;
    }

        /* Copy the old data. */
    
    oldsize = blk_size(oldblock) * WSIZE;
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);




    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/* 
 * checkheap - We don't check anything right now. 
 */
void mm_checkheap(int verbose)  
{ 
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static struct block *extend_heap(size_t words) 
{
    void *bp;

    /* Allocate an even number of words to maintain alignment */
    words = (words + 1) & ~1;
    if ((long)(bp = mem_sbrk(words * WSIZE)) == -1)  
        return NULL;

    /* Initialize free block header/footer and the epilogue header.
     * Note that we scoop up the previous epilogue here. */
    struct block * blk = bp - sizeof(FENCE);
    mark_block_free(blk, words);
    next_blk(blk)->header = FENCE;

    /* Coalesce if the previous block was free */
    //printf("i am here.");
    return coalesce(blk);
}

/* 
 * place - Place block of asize words at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(struct block *bp, size_t asize, int mode)
{
    if(mode == 1)
    {
        RB_REMOVE(mytree, &tree, bp);
    }

    size_t csize = blk_size(bp);

    if ((csize - asize) >= MIN_BLOCK_SIZE_WORDS) { 
        mark_block_used(bp, asize);
        bp = next_blk(bp);
        mark_block_free(bp, csize-asize);

        RB_INSERT(mytree, &tree, bp);
    }
    else { 
        mark_block_used(bp, csize);
    }
}

/* 
 * find_fit - Find a fit for a block with asize words 
 */
static struct block *find_fit(size_t asize)
{
    struct block a;
    a.header.size = asize;
    struct block * p = RB_NFIND(mytree, &tree, &a);
    if(p == NULL)
    {
        return NULL;
    }
    else
    {
       // printf("Found a good match!\n");
        RB_REMOVE(mytree, &tree, p);
        return p;
    }
}
