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
static void place(void *bp, size_t asize);
void mm_free(void *bp);

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

#define WSIZE 4 // word and header footer 사이즈를 byte로. 
#define DSIZE 8 // double word size를 byte로
#define CHUNKSIZE (1<<12) // heap을 늘릴 때 얼만큼 늘릴거냐? 4kb 분량.

#define MAX(x,y) ((x)>(y)? (x) : (y)) // x,y 중 큰 값을 가진다.

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), 헤더에서 써야하기 때문에 만듬.
#define PACK(size,alloc) ((size)| (alloc)) // alloc : 가용여부 (ex. 000) / size : block size를 의미. =>합치면 온전한 주소가 나온다.

/* address p위치에 words를 read와 write를 한다. */
#define GET(p) (*(unsigned int*)(p)) // 포인터를 써서 p를 참조한다. 주소와 값(값에는 다른 블록의 주소를 담는다.)을 알 수 있다. 다른 블록을 가리키거나 이동할 때 쓸 수 있다. 
#define PUT(p,val) (*(unsigned int*)(p)=(int)(val)) // 블록의 주소를 담는다. 위치를 담아야지 나중에 헤더나 푸터를 읽어서 이동 혹은 연결할 수 있다.

// address p위치로부터 size를 읽고 field를 할당
#define GET_SIZE(p) (GET(p) & ~0x7) // '~'은 역수니까 11111000이 됨. 비트 연산하면 000 앞에거만 가져올 수 있음. 즉, 헤더에서 블록 size만 가져오겠다.
#define GET_ALLOC(p) (GET(p) & 0x1) // 00000001이 됨. 헤더에서 가용여부만 가져오겠다.

/* given block ptr bp, header와 footer의 주소를 계산*/
#define HDRP(bp) ((char*)(bp) - WSIZE) // bp가 어디에있던 상관없이 WSIZE 앞에 위치한다.
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더의 끝 지점부터 GET SIZE(블록의 사이즈)만큼 더한 다음 word를 2번빼는게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작 위치가 된다.

/* GIVEN block ptr bp, 이전 블록과 다음 블록의 주소를 계산*/
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp)-WSIZE))) // 그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동 -> 그 다음 블록의 헤더 뒤로 감.)
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 그 전 블록의 bp위치로 이동.(이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동.)
static char *heap_listp;  // 처음에 쓸 큰 가용블록 힙을 만들어줌.
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding 블록이 32비트 시스템에서 8바이트 단위로 정렬되어야 할때, 4바이트를 더 추가해줌*/
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) // 동적할당 함수 구현하기
{
    size_t asize;                   // 정렬조건에 만족하는 값을 저장할 변수
    size_t extendsize;              // 공간이 없는 경우, 확장할 공간의 크기를 저장할 변수
    char *bp;                       // 어떤 블록을 가르킬지 저장하는 포인터 변수
    if (size == 0){                 // size 0인경우,
        return NULL;
    }                               // 메모리 할당이 필요 없으므로, NULL반환
    if (size <= DSIZE){             // size가 DSIZE이하인 경우
        asize = 2*DSIZE;            // 최소 블록 크기인 2*DSZIE로 설정
    }                                
    else {                          // size가 DSIZE를 초과하면
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);         // 블록 크기를 계산해(공식임) 블록 크기를 설정
    }
    if ((bp = find_fit(asize)) != NULL) {              // 할당 가능한 메모리 블록 찾기(요청된 크기에 맞는 블록)가 성공하면,
        place(bp, asize);                              // 블록을 할당하고
        return bp;                                     // 해당 블록의 포인터를 반환
    }
    extendsize = MAX(asize,CHUNKSIZE);  // asize랑 CHUNKSIZE 중에 큰 값을 저장하고
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) // 확장할 수 있는 장소가 없을 경우
        return NULL; // 널 리턴
    place(bp, asize); // 확장한 블록을 할당하고,
    return bp; // 해당 블록의 포인터를 반환
}
static void *find_fit(size_t asize)
{
    void *bp; // 공간을 찾을 포인터 변수 선언
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // heap_listp부터 모든 블록을 순회, 블록 크기가 0인 블록은 힙의 끝을 나타냄
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // 블록이 할당되지 않았고, 요청된 크기보다 크거나 같은 크기의 블록이라면
            return bp; // 해당 블록의 포인터를 반환
        }
    }
    return NULL; // 할당 가능한 블록이 없을 경우 NULL 반환
}

static void *next_fit(size_t asize)
{
    void *bp; // 공간을 찾을 포인터 변수 선언
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // heap_listp부터 모든 블록을 순회, 블록 크기가 0인 블록은 힙의 끝을 나타냄
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // 블록이 할당되지 않았고, 요청된 크기보다 크거나 같은 크기의 블록이라면
            return bp; // 해당 블록의 포인터를 반환 
        }
    }
    return NULL; // 할당 가능한 블록이 없을 경우 NULL 반환
}
/*
 * mm_free - Freeing a block does nothing.
 */

void *mm_realloc(void *ptr, size_t size) // 지금 할당된 공간을 아예 이사시키는 함수
{

    void *oldptr = ptr; // 이전 공간을 나타내는 변수
    void *newptr; // 이사갈 공간 변수
    size_t copySize; // 이삿짐이 얼마나 많은지를 저장
    newptr = mm_malloc(size); // 새로운 메모리 블록 할당

    if (newptr == NULL) // 새로운 메모리 블록 할당에 실패한 경우
      return NULL; // 함수 종료
    copySize = GET_SIZE(HDRP(ptr)); // 이전 메모리 블록의 크기 가져오기
    if (size < copySize) // 요청 된 크기가 복사할 크기보다 작은 경우
      copySize = size; // 복사사이즈를 사이즈로 조정
    memcpy(newptr, oldptr, copySize); // 이전 메모리 블록의 데이터를 새로운 메모리 블록으로 복사
    mm_free(oldptr); // 이전 메모리 블록을 해제
    return newptr; // 새로운 메모리 블록의 포인터 반환
}


static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;    
    }
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기 저장
    if ((csize - asize) >= (2*DSIZE)) { // 현재 블록의 크기에서 요청된 블록의 크기를 뺀 값이 최소 블록 크기보다 크거나 같다면
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록의 요청된 블록사이즈만큼 저장(딱 맞게)
        PUT(FTRP(bp), PACK(asize, 1)); // 마찬가지
        bp = NEXT_BLKP(bp); // bp를 다음 bp로 바꿈
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 다음 블록을 비워둠(남은 거 비워두기)
        PUT(FTRP(bp), PACK(csize-asize, 0)); // 다음 블록을 비워둠(마찬가지))
    }
    else { //가용 블록(현재 블록)의 크기가 부족하다면
        PUT(HDRP(bp), PACK(csize, 1)); // 그냥 다 써라
        PUT(FTRP(bp), PACK(csize, 1)); // 너 다 해라
    }
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 헤더에서 읽어옴
    // 현재 블록의 헤더와 푸터의 할당상태를 0으로 설정하여 해제
    PUT(HDRP(bp), PACK(size, 0)); // 현재 블록의 헤더의 크기와 할당상태를 설정
    PUT(FTRP(bp), PACK(size, 0)); // 푸터도 크기와 할당상태를 설정
    // 인접한 빈 블록들을 병합하여 하나의 큰 블록으로 재배치
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp; 
}











