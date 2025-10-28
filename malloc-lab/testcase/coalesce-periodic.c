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
#define CHUNKSIZE (1<<12)
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
static void coalesce_periodic(void);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_node(void *bp);
static void remove_node(void *bp);


static char *heap_listp = 0;  // 힙 시작점
static char *free_listp = 0;  // 명시적 가용 리스트의 첫 블록
static int free_count = 0;    // 추가: free 호출 횟수 카운터
#define COALESCE_THRESHOLD 10  // 추가: 10번마다 연결

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

    /*(테스트케이스에 한해서) 자주사용되는 작은 블럭이 잘 처리되어 점수가 오르는 것*/
    /*extend_heap에서 처리를 안해줘서 일단은 오류나는듯*/
    // if (extend_heap(4)==NULL)       
    //     return -1;

    // 첫 확장
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}


/*계산식을 굳이 안쓰고 word 대신 byte를 써보기 malloc 함수에 역할 모두 맡기기*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);  // 즉시 연결 복원
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= 2*DSIZE)
        asize = 4*DSIZE; 
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    // 지연 연결 로직 제거 - 원래대로
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
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
    insert_node(ptr);
    
    // 주기적 연결 로직
    free_count++;
    if (free_count >= COALESCE_THRESHOLD) {
        coalesce_periodic();
        free_count = 0;
    }
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

static void coalesce_periodic(void)
{
    void *bp = heap_listp;
    
    while (GET_SIZE(HDRP(bp)) > 0) {
        if (!GET_ALLOC(HDRP(bp))) {
            void *current = bp;
            size_t total_size = GET_SIZE(HDRP(bp));
            void *next_bp = NEXT_BLKP(bp);
            
            while (GET_SIZE(HDRP(next_bp)) > 0 && 
                   !GET_ALLOC(HDRP(next_bp))) {
                remove_node(next_bp);
                total_size += GET_SIZE(HDRP(next_bp));
                next_bp = NEXT_BLKP(next_bp);
            }
            
            if (total_size > GET_SIZE(HDRP(current))) {
                remove_node(current);
                PUT(HDRP(current), PACK(total_size, 0));
                PUT(FTRP(current), PACK(total_size, 0));
                insert_node(current);
            }
            
            bp = NEXT_BLKP(current);
        } else {
            bp = NEXT_BLKP(bp);
        }
    }
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
    for (bp = free_listp; bp != NULL; bp = SUCC(bp)) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;
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
        coalesce(bp);  // 즉시 연결 복원
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}