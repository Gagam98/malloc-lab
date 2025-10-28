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
    "team 1",
    /* First member's full name */
    "choi",
    /* First member's email address */
    "email@email",
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
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


static char *heap_listp = 0;  // 힙 시작점
#define NUM_CLASSES 10  // 크기 클래스 개수
static char *seg_list[NUM_CLASSES];  // 각 크기 클래스별 free list 헤드

// 블록 크기에 맞는 클래스 인덱스 반환
static int get_class(size_t size)
{
    // 크기 클래스: 
    // 0: 16-31
    // 1: 32-63
    // 2: 64-127
    // 3: 128-255
    // 4: 256-511
    // 5: 512-1023
    // 6: 1024-2047
    // 7: 2048-4095
    // 8: 4096-8191
    // 9: 8192+
    
    if (size <= 32) return 0;
    if (size <= 64) return 1;
    if (size <= 128) return 2;
    if (size <= 256) return 3;
    if (size <= 512) return 4;
    if (size <= 1024) return 5;
    if (size <= 2048) return 6;
    if (size <= 4096) return 7;
    if (size <= 8192) return 8;
    return 9;
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));

    heap_listp += (2*WSIZE);
    
    // 기존: free_listp = NULL;
    // 새로 추가: 모든 segregated list 초기화
    for (int i = 0; i < NUM_CLASSES; i++) {
        seg_list[i] = NULL;
    }
    /*(테스트케이스에 한해서) 자주사용되는 작은 블럭이 잘 처리되어 점수가 오르는 것*/
    /*extend_heap에서 처리를 안해줘서 일단은 오류나는듯*/
    // if (extend_heap(4)==NULL)       
    //     return -1;

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

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

    /* 적합한 블록 없음. 힙 확장 */
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
    coalesce(ptr);
}

static void insert_node(void *bp)
{
    if (bp == NULL) return;
    
    size_t size = GET_SIZE(HDRP(bp));
    int class = get_class(size);  // 크기에 맞는 클래스 찾기
    
    // 해당 클래스의 리스트 맨 앞에 삽입 (LIFO)
    SUCC(bp) = seg_list[class];
    PRED(bp) = NULL;
    if (seg_list[class] != NULL)
        PRED(seg_list[class]) = bp;
    seg_list[class] = bp;
}

static void remove_node(void *bp)
{
    if (bp == NULL) return;
    
    size_t size = GET_SIZE(HDRP(bp));
    int class = get_class(size);  // 크기에 맞는 클래스 찾기
    
    if (PRED(bp))
        SUCC(PRED(bp)) = SUCC(bp);
    else
        seg_list[class] = SUCC(bp);  // 첫 번째 노드면 헤드 업데이트
    
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
    int class = get_class(asize);
    void *best_fit = NULL;
    size_t min_diff = (size_t)-1;
    
    // 해당 클래스부터 상위 클래스까지 탐색
    for (int i = class; i < NUM_CLASSES; i++) {
        void *bp;
        
        // 각 클래스 내에서 best-fit 탐색
        for (bp = seg_list[i]; bp != NULL; bp = SUCC(bp)) {
            size_t block_size = GET_SIZE(HDRP(bp));
            
            if (asize <= block_size) {
                size_t diff = block_size - asize;
                
                // 완벽한 fit 발견 시 즉시 반환
                if (diff == 0) {
                    return bp;
                }
                
                // 더 나은 fit 발견
                if (diff < min_diff) {
                    min_diff = diff;
                    best_fit = bp;
                }
            }
        }
        
        // 현재 클래스에서 찾았으면 반환 (상위 클래스 탐색 불필요)
        if (best_fit != NULL) {
            return best_fit;
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
        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}