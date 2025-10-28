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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/*전역변수*/
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*기본 상수 정의*/
#define WSIZE 4     //32비트 워드 크기
#define DSIZE 8
// #define CHUNKSIZE (1<<12)
#define MAX(x,y) ((x) > (y) ? (x):(y))

/*크기와 할당 비트를 하나의 워드로 패킹*/
#define PACK(size, alloc) ((size) | (alloc))

/*주소 p에서 워드 읽기/쓰기*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p)=(val))

/*주소 p에서 크기와 할당 비트 읽기*/
#define GET_SIZE(p) (GET(p)&~0x7)
#define GET_ALLOC(p) (GET(p)&0x1)

/*블록 포인터 bp로 헤더와 푸터 주소 계산*/
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp))-DSIZE)

/*블록 포인터 bp로 다음/이전 블록 주소 계산*/
#define NEXT_BLKP(bp) ((char *)(bp)+GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* explicit free list용 매크로 (수정된 안전한 버전) */
#define PRED_PTR(bp) ((char **)(bp))        /* pred 저장 위치 (bp) */
#define SUCC_PTR(bp) ((char **)(bp) + 1)    /* succ 저장 위치 (bp + sizeof(void *)) */
#define PRED(bp) (*(PRED_PTR(bp)))
#define SUCC(bp) (*(SUCC_PTR(bp)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


static char *heap_listp = 0;  // 힙 시작점
static char *free_listp = 0;  // 명시적 가용 리스트의 첫 블록


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // prologue(4워드) + epilogue(1워드) = 5워드 필요
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            // Alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));   // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));   // Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));       // Epilogue header

    heap_listp += (2*WSIZE);                       // Prologue footer 뒤로 이동
    free_listp = NULL;

    return 0;
}


/*계산식을 굳이 안쓰고 word 대신 byte를 써보기 malloc 함수에 역할 모두 맡기기*/
static void *extend_heap(size_t words)
{
    char *bp; //블록 포인터
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

void *mm_malloc(size_t size)
{
    size_t asize;      /* 조정된 블록 크기 */
    size_t extendsize; /* 적합한 블록 없을 때 힙 확장 크기 */
    char *bp;

    /* 가짜 요청 무시 */
    if (size == 0)
        return NULL;

    /* 오버헤드와 정렬 요구사항 포함하여 블록 크기 조정 */
    // Explicit list를 위해 최소 블록 크기를 32바이트로
    // 헤더(4) + PRED(8) + SUCC(8) + 푸터(4) = 24바이트 필요
    // 정렬을 위해 32바이트 사용
    if (size <= 2*DSIZE)
        asize = 4*DSIZE; 
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* 자유 리스트에서 적합한 블록 검색 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 적합한 블록 없음. 요청된 크기만큼만 힙 확장 */
    extendsize = asize;
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
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

static void insert_node(void *bp)
{
    if (bp == NULL) return;

    SUCC(bp) = free_listp;
    PRED(bp) = NULL;
    if (free_listp != NULL)
        PRED(free_listp) = bp;
    free_listp = bp;
}

static void remove_node(void *bp)
{
    if (bp == NULL) return;
    
    if (PRED(bp))
        SUCC(PRED(bp)) = SUCC(bp);
    else
        free_listp = SUCC(bp);
    if (SUCC(bp))
        PRED(SUCC(bp)) = PRED(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        insert_node(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        remove_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        remove_node(PREV_BLKP(bp));
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_node(bp);
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
    size_t asize;
    size_t oldsize;

    if (ptr == NULL)
        return mm_malloc(size);

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // 크기 조정 (mm_malloc과 동일하게)
    if (size <= 2*DSIZE)
        asize = 4*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    oldsize = GET_SIZE(HDRP(oldptr));

    // Case 1: 기존 블록이 충분히 크면 그대로 사용
    if (oldsize >= asize) {
        return oldptr;
    }

    // Case 2: 다음 블록이 free이고 합치면 충분한지 체크
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));

    if (!next_alloc && (oldsize + next_size) >= asize) {
        // 다음 블록을 free list에서 제거하고 병합
        remove_node(NEXT_BLKP(oldptr));
        size_t total_size = oldsize + next_size;
        PUT(HDRP(oldptr), PACK(total_size, 1));
        PUT(FTRP(oldptr), PACK(total_size, 1));
        return oldptr;
    }

    // Case 3: 제자리 확장 불가능 -> 새로 할당
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    copySize = oldsize - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}


static void *find_fit(size_t asize)
{
    void *bp;
    void *best_fit = NULL;
    size_t min_diff = (size_t)-1;  // 최대값으로 초기화

    for (bp = free_listp; bp != NULL; bp = SUCC(bp)) {
        size_t block_size = GET_SIZE(HDRP(bp));
        
        if (asize <= block_size) {
            size_t diff = block_size - asize;
            
            // 완벽한 fit을 찾으면 즉시 반환 (최적화)
            if (diff == 0) {
                return bp;
            }

            size_t remainder;
            if (diff >= (2 * DSIZE)) {
                remainder = diff;  // 분할 가능 - 실제로 남는 크기
            } else {
                remainder = 0;     // 분할 불가 - 남는 공간 없음 (전체 사용)
            }
            
            // 더 작은 차이를 가진 블록 발견
            if (diff < min_diff) {
                min_diff = diff;
                best_fit = bp;
            }
        }
    }
    
    return best_fit;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    remove_node(bp);

    if ((csize - asize) >= (4 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}