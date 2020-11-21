/*///
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *  My mm.c file is implemented using a segregated list of 12 bins, this was  *
 *  decided by using powers of 2 from 32 onward. mm.c also has funtionality   *
 *  that removes the footers from the blocks by masking the write_header fcns *
 *  with a defined 0x02 constant. My mm_checkheap function prints out the     *
 *  buckets, prints out each bucket's contents, and also prints out where     *
 *  the program is operating in terms of the methods. Additionally, the check *
 *  heap function will print out all blocks in memory from the heap_start.    *
 *                                                                            *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
//#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif


/* Basic constants */
//This is the number of buckets that we have in the array
#define seg_size 12
//This is the allocation bit for determining 
//whether or not a block has been allocated
#define alloc_bit 0x02
//This is used to make it easier to refer to 
//the previous block from the passed block
#define PBLOCK block->block_payload.block_ties.previous
//This is used to make it easier to refer to the next block from the passed block
#define NBLOCK block->block_payload.block_ties.next

typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block block_t;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    union //Based off of Noah's Suggestion, use a union for storage
    {
        struct 
        {
            block_t *next; //Pointer to the Next Block
            block_t *previous; //Pointer to the Previous Block

        } block_ties;

        char payload[0];
    
    } block_payload;
    
    //Pointers to the previous and next blocks from the current block
    // struct block * next_block;
    // struct block * previous_block;
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;

/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;
//This represents an array of pointers where blocks of memory will be placed.
static block_t *segregrated_list[12]; 

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);


static block_t *find_next(block_t *block);
static block_t *find_prev(block_t *block);
static word_t *find_prev_footer(block_t *block);

//Heap Checker Functions
bool mm_checkheap(int lineno);
static void checkblock(block_t *block);

//Functions that I declared:
//1. Utility Functions for getting the footer size and footer pointers
static word_t get_footer_pointer(block_t *block);
static word_t get_footer(block_t *block);

//2. Utility Functions for placing blocks
//Used to determine which size class a block belongs in
static int sizeIndex(size_t size);
//Used to insert a block into a specific seg. list
static void insertion(block_t * block, size_t size);
//Used to delete a block from a seg. list
static void deletion(block_t * block);
//Used to find whether or not the previous block has been allocated
static bool get_previous_allocation(block_t *block);

//Defining Function that provides information 
//on which size class a block belongs in
//for a segregated free list. Doing this with 
//powers of 2 starting from 32, up to 11 buckets.
static int sizeIndex(size_t size) {
    int start = 0;
    switch(start) {
        case 0:
            if (size < 32) {
                return 0;
            }
        case 1:
            if ((size >= 32) && (size < 64)) {
                return 1;
            }
        case 2:
            if ((size >= 64) && (size < 128)) {
                return 2;
            }
        case 3:
            if ((size >= 128) && (size < 256)) {
                return 3;
            }
        case 4:
            if ((size >= 256) && (size < 512)) {
                    return 4;
                }
        case 5:
            if ((size >= 512) && (size < 1024)) {
                return 5;
            }
        case 6:
            if ((size >= 1024) && (size < 2048)) {
                return 6;
            }
        case 7:
            if ((size >= 2048) && (size < 4096)) {
                return 7;
            }
        case 8:
            if ((size >= 4096) && (size < 8192)) {
                return 8;
            }
        case 9:
            if ((size >= 8192) && (size < 16384)) {
                return 9;
            }
        case 10:
            if ((size >= 16384) && (size < 32768)) {
                return 10;
            }
    }
    return 11;
}

/*
The insertion Method Inserts a block into it's 
respective segregated list based on it's size.
*/
static void insertion(block_t *block, size_t size) { 
    dbg_printf("\nInserting Block of Size %lu", size);
    //If block is null, we can't insert, so just return
    if (block == NULL) {
        return;
    }
    //Case 1: if the block being inserted is not the first block, 
    //we need to create a temp. block to store information and
    //interchange the position while preserving information.
    // We also need to update the previous and next pointers
    if (segregrated_list[sizeIndex(size)] != NULL) {
        block_t *placeholder = segregrated_list[sizeIndex(size)];
        NBLOCK = placeholder;
        placeholder->block_payload.block_ties.previous = block;
        PBLOCK = NULL;
        segregrated_list[sizeIndex(size)] = block;
        return;
    }
    //Case 2: If the block being inserted is the first block, 
    //just set the first block of the seg. list to that block, and
    //set the next and previous pointers
    if (segregrated_list[sizeIndex(size)] == NULL) {
        segregrated_list[sizeIndex(size)] = block;
	    segregrated_list[sizeIndex(size)]->block_payload.block_ties.previous = NULL;
	    segregrated_list[sizeIndex(size)]->block_payload.block_ties.next = NULL;
        return;
    }
}

/*
*The deletion method deletes a block from it's respective seg. list
*We test four different cases based 
*on the status of the previous and next blocks.
*/
static void deletion(block_t *block) {
    block_t *block_next = NBLOCK;
    block_t *block_previous = PBLOCK;
    size_t size = get_size(block);
    dbg_printf("\nDeleting Block--> Size:%li | Pointer:%p",size,block);
    
    //Case 1: If it is the only block in the list, just set front to NULL
    if (block_next == NULL && block_previous == NULL) {
        segregrated_list[sizeIndex(size)] = NULL;
        return;
    }
    // Case 2: If there is a previous block, 
    // set the previous block's next pointer to null
    if (block_next == NULL && block_previous != NULL) {
        block_previous->block_payload.block_ties.next = NULL;
        return;
    }
    //Case 3: If there is a next block, 
    //set the next block's previous pointer to null and set the pointer
    //of the respective seg. list equal to the next block
    if (block_next != NULL && block_previous == NULL) {
        block_next->block_payload.block_ties.previous = NULL;
        segregrated_list[sizeIndex(size)] = block_next;
        return;
    }
    //Case 4: If both the next and previous pointers exist, 
    //then we need to remove the block between them.
    if (block_next != NULL && block_previous != NULL) {
        block_previous->block_payload.block_ties.next = block_next;
        block_next->block_payload.block_ties.previous = block_previous;
        return;
    }
}

/*
 * This function initializes the heap.
 * The main purpose is to initialize all 
 * of the buckets of segregated list to <NULL>
 */
bool mm_init(void)
{
    // Create the initial empty heap
    dbg_printf("\nINIT"); 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));
    int i;

    if (start == (void *)-1)
    {
        return false;
    }

    //Prologue footer, bitwise or with the alloc bit
    start[0] = pack(0, true)|alloc_bit;
    //Epilogue header, bitwise or with the alloc bit
    start[1] = pack(0, true)|alloc_bit;

    // Heap starts with first "block header", 
    //currently the epilogue footer
    heap_start = (block_t *) &(start[1]);

    //Initialize the free list to start with NULL
    //Initialize each bucket in the seg list to start with NULL
    for (i = 0; i < seg_size; i++) {
        segregrated_list[i] = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * This function allocates a block, rounded to the nearest 16 bytes.
 * If there is no block found, 
 * extendHeap is called and more memory is allocated.
 * All allocated blocks will not be available until they are freed
 */
void *malloc(size_t size) 
{
    dbg_printf("\nMALLOC");
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead 
    // and to meet alignment requirements
    asize = max(round_up(size + wsize, dsize), min_block_size);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }
    place(block, asize);
    bp = header_to_payload(block);
    dbg_printf("\nMALLOCing SIZE: %lx", asize);
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
    } 

/*
 * The Free method frees blocks that are to be deallocated
 * The blocks that are freed are available to malloc()
 */
void free(void *bp)
{
    dbg_printf("\nFREE");
    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    //Find the alloc bit
    int extract = (block->header) & alloc_bit; 

    //Carry the alloc bit to free
    write_header(block, size|extract, false); 
    write_footer(block, size, false);
    block_t *next_block = find_next(block);
    //Clear alloc bit flag for free
    next_block->header = next_block->header & (~alloc_bit); 

    coalesce(block);

}

/*
 * realloc returns a pointer to an allocated region
 * If the size is zero, we free  and return null
 * if the pointer is null, we malloc size
 * if the new pointer is null, we return null
 */
void *realloc(void *ptr, size_t size)
{
    dbg_printf("\nREALLOC");
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc allocates a block space in memory with malloc, and then
 * initializes that allocated space to 0
 */
void *calloc(size_t elements, size_t size)
{
    dbg_printf("\nCALLOC");
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {    
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 * extend heap extends the heap by a specific amount of bytes
 */
static block_t *extend_heap(size_t size) 
{
    dbg_printf("\nEXTEND HEAP");
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    word_t extract = ((block->header) & alloc_bit); //Find the alloc bit
    write_header(block, size|extract, false);
    write_footer(block, size|extract, false);
    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

static bool get_previous_allocation(block_t *block) {
    if ((block->header) & alloc_bit) {
        return true;
    }
    return false;
}


/*
 * The Coalesce method coalesces the 
 * blocks with previous and next blocks if either 
 * or both are unallocated. This will return a 
 * POINTER to the coalesced block.
 * After coalescing, the previous and next blocks must be allocated.
 */
static block_t *coalesce(block_t *block) //DONE WITH ALLOC BIT
{
    dbg_printf("\nCOALESCE");
    bool previous_allocation = get_previous_allocation(block);
    bool next_allocation = get_alloc(find_next(block));
    size_t size = get_size(block);

    if (previous_allocation && next_allocation) { //Case 1
        
        dbg_printf("...Case 1: Previous Alloc: %d"
                    "| Next Alloc: %d",previous_allocation, next_allocation);
        insertion(block, size);
        return block;

    } else if (previous_allocation && !next_allocation) { //Case 2
        dbg_printf("...Case 2: Previous Alloc: %d" 
                    "| Next Alloc: %d",previous_allocation, next_allocation);
        block_t *next = find_next(block);
        size += get_size(find_next(block));
        deletion(next);
        write_header(block, size + alloc_bit, false);
        write_footer(next, size + alloc_bit, false);
        insertion(block, size);
        return block;

    } else if (!previous_allocation && next_allocation) { //Case 3
        dbg_printf("...Case 3: Previous Alloc: %d"
                    "| Next Alloc: %d",previous_allocation, next_allocation);
        block_t * previous = find_prev(block);
        size += get_size(find_prev(block));
        deletion(previous);
        word_t extract = ((previous->header) & alloc_bit);
        write_header(previous, size|extract, false);
        write_footer(block, size|extract, false);
        block = previous;
        insertion(block, size);
        return block;

    } else { //Case 4
        dbg_printf("...Case 4: Previous Alloc: %d"
                    "| Next Alloc: %d",previous_allocation, next_allocation);
        block_t * previous = find_prev(block);
        block_t * next = find_next(block);
        size += get_size(next) + get_size(previous);
        deletion(previous);
        deletion(next);
        word_t extract = ((previous->header) & alloc_bit);
        write_header(previous, size|extract, false);
        write_footer(next, size|extract, false);
        block = previous;
        insertion(block, size);
        return block;
    }
}

/*
 * Places a block at the beginning of 
 * the pointer, will then split the block
 * to encompass the allocation requirement, 
 * whilst keeping the other partition as free.
 * This method requires that the block is initially unallocated
 */
static void place(block_t *block, size_t asize) //DONE WITH ALLOC BIT
{
    dbg_printf("\nPLACE %p", block);
    dbg_printf("\nPlacing Block: %p, of Size: %lx",block, asize);
    size_t csize = get_size(block);
    int extract = (block->header) & alloc_bit;

    if ((csize - asize) >= min_block_size)
    {
        block_t *block_next;
        deletion(block);
        write_header(block, asize|extract, true);
        write_footer(block, asize|extract, true);
        block_next = find_next(block);
        write_header(block_next, csize-asize+alloc_bit, false);
        write_footer(block_next, csize-asize+alloc_bit, false);
        coalesce(block_next);
    }

    else
    {
        deletion(block);
        write_header(block, csize|alloc_bit, true);
        write_footer(block, csize|alloc_bit, true);
    }
    dbg_ensures(mm_checkheap(__LINE__));
}

/*
 * Find fit finds the fit in a respective segregated list for a block
 * ->This algorithm uses the first fit and best fit
 * --> We first find the block fit by 
 *       running first fit, and then we use that block and
 * --> run it through 25 seaches for the best fit. 
 *       If we cannot find a best fit within 25 searches,
 *       we just return the original block
 */
static block_t *find_fit(size_t asize) {
    dbg_printf("\nFinding Fit for Size: %lx", asize);
    block_t *block;
    block_t *bestblock = NULL;
    int correct_size;
    int i = 0;
    int bfit_thresh = 25;
    for (correct_size = sizeIndex(asize); correct_size != seg_size; correct_size++) {
        for (block = segregrated_list[correct_size]; block != NULL; 
                    block = block->block_payload.block_ties.next) {
             if (!(get_alloc(block)) && (asize <= get_size(block))) {
                bestblock = block;
                break;
            }
        }
        if (bestblock != NULL) {
            break;
        }
   }
   if (bestblock == NULL) {
       return NULL;
   }
   for (block = segregrated_list[correct_size]; block != NULL; 
            block = block->block_payload.block_ties.next) {
     if (block->block_payload.block_ties.next == NULL) {
           return bestblock;
       } else if (get_size(block) < get_size(bestblock) && asize <=get_size(block)) {
           bestblock = block;
       }
     i++;
     if (i > bfit_thresh) {
         break;
     }
   }
   return bestblock;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | alloc_mask) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block->header = pack(size, alloc);
    block_t *helper;
    if (alloc) {
        helper = find_next(block);
        if (helper == block) {
            return;
        }
        helper->header = helper->header | alloc_bit;
    }
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
    word_t *footerp = (word_t *)((block->block_payload.payload) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}

/*
*This is my function: we pull some data from write 
* footer rather than rewriting the entire function
* Purpose is to get a footer pointer, and
* then use that information to get the actual footer
*/

static word_t get_footer_pointer(block_t *block)
{
    word_t *footerp = (word_t *)((block->block_payload.payload) + get_size(block) - dsize);
    return *footerp;
}

static word_t get_footer(block_t *block)
{
    return get_footer_pointer(block);
    
}

    /*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
    static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, block_payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->block_payload.payload);
}

/* 
 * 1. My heapchecker prints out each bucket in the segregated list
 * -->At each bucket, there is a linked list of blocks, all of the pointers are printed out
 * 2. We check to see if the links between the next and previous blocks
 *  are the same, if the next block is not null and, if next->previous is not start
 * 3. We check to see if the links between the next and previous blocks 
 * are the same, if the previous block is not null and, if previous->next is not start
 * 4. We check to make sure that the sizeIndex of start 
 * is the correct i, if it is not in the correct bucket, we throw an error. 
 * 5. We check to make sure that the blocks are 16 byte aligned
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)
{
    block_t *previous;
    block_t *next;
    block_t *start;
    block_t *iter;
    dbg_printf("\n\nSegregated List Print Out\n");
    int i;
    //This for loop prints out each bin in the segregated list, 
    //and for each bin, each block located in that bin.
    for (i = 0; i < seg_size; i++) {
        start = segregrated_list[i];
        dbg_printf("\nLIST[%d]: ",i);
        for (iter = start; iter != NULL; iter = next) {
            dbg_printf("pt->%p", iter);
            previous = iter->block_payload.block_ties.previous;
            next = iter->block_payload.block_ties.next;
            if (next != NULL) {
                if (next->block_payload.block_ties.previous != iter) {
                    printf("Links is not the same between previous block:"
                    "%p and next block: %p", previous, next);
                    return false;
                }
            }
            if (previous != NULL) {
                if (previous->block_payload.block_ties.next != iter) {
                    printf("Link is not the same between previous block:" 
                            "%p and next block: %p", previous, next);
                    return false;
                }
            }
            if (sizeIndex(get_size(iter)) != i) {
                printf("Class Size wrong, as block size isnt in that bucket");
                return false;
            }
            checkblock(iter);
        }
    }
    //This is used to print out all of the blocks in memory from the heap start
    for (next = heap_start; get_size(next) != 0; next = find_next(next)) {
        dbg_printf("%p:\t size: %lx\t alloc: %d\t"
                   "prev_alloc: %d\t prev_size: %lx\n",
                   next, get_size(next), get_alloc(next),
                   get_previous_allocation(next),
                   extract_size(*find_prev_footer(next)));
    }
    return true;
}

static void checkblock(block_t *block) { //Check that the blocks are 16 byte aligned
    if (get_size(block) % 16 || (size_t)block->block_payload.payload % 16)
    {
        printf("Error: %p is not doubleword aligned\n", block);
    }
}
