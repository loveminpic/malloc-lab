/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);
void mm_free(void *bp);
static void *next_fit(size_t asize);
void removeBlock(void *bp);
void putFreeBlock(void *bp);

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "3 team",
    /* First member's full name */
    "Minji Lee",
    /* First member's email address */
    "minji0479@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 
#define DSIZE 8 
#define CHUNKSIZE (1<<10) 

#define MAX(x,y) ((x)>(y)? (x) : (y)) 

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), 헤더에서 써야하기 때문에 만듬.
#define PACK(size,alloc) ((size)| (alloc)) 

/* address p위치에 words를 read와 write를 한다. */
#define GET(p) (*(unsigned int*)(p)) 
#define PUT(p,val) (*(unsigned int*)(p)=(int)(val)) 

// address p위치로부터 size를 읽고 field를 할당
#define GET_SIZE(p) (GET(p) & ~0x7) 
#define GET_ALLOC(p) (GET(p) & 0x1) 

/* given block ptr bp, header와 footer의 주소를 계산*/
#define HDRP(bp) ((char*)(bp) - WSIZE) 
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) 
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) 

#define SUCP(bp) (*(void **)(bp))
#define PREP(bp) (*(void **)(bp + WSIZE))

static char *heap_listp = NULL;             // 처음에 쓸 큰 가용블록 힙을 만들어줌.
static char *free_listp = NULL; 

/* 
 * mm_init - initialize the malloc package.
 */

static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);
void removeBlock(void *);
void putFreeBlock(void *);
// static void *find_nextp; // next fit
static char *heap_listp; // points to the prologue block or first block
static char *free_listp;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap*/
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE*2, 1)); /* Prologue header */
    
    PUT(heap_listp + (2*WSIZE), (int)NULL); /* Prologue SUCCESOR, 제일 처음은 root 역할 */
    PUT(heap_listp + (3*WSIZE), (int)NULL); /* Prologue PREDECCESSOR */

    PUT(heap_listp + (4*WSIZE), PACK(DSIZE*2, 1)); /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));     /* Epilogue header */
    free_listp = heap_listp + DSIZE; 
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) // mem_brk지점을 old_ptr로 반환함.
    return NULL;

    /* Allocate an even number of words to maintain alignment */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */ //끝 부분이라서 이전께 비었는지 확인만 하면 됨
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /* 책 내용 */
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    /* Ignore spurious requests */ 
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ( ( size + (DSIZE) + (DSIZE-1) ) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

   /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) 
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */

void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc)
    { /* Case 2 */
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else if (!prev_alloc && !next_alloc)
    { /* Case 4 */
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } 

    putFreeBlock(bp);

    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    if (oldptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    if (newptr == NULL){
      return NULL;
    }
    
    if (size < copySize) { 
      copySize = size;
    }
  
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCP(bp))
    {
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    removeBlock(bp);
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        putFreeBlock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void putFreeBlock(void *bp){
    PREP(bp) = NULL;
    SUCP(bp) = free_listp;
    PREP(free_listp) = bp;
    free_listp = bp;
}

void removeBlock(void *bp){

    if (bp == free_listp){
        PREP(SUCP(bp)) = NULL;
        free_listp = SUCP(bp);
    }
    else{
        SUCP(PREP(bp)) = SUCP(bp);
        PREP(SUCP(bp)) = PREP(bp);
    }

}