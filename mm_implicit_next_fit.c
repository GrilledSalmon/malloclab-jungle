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
    "Salmon",
    /* First member's full name */
    "Yoonwoo Kye",
    /* First member's email address */
    "mryoonwoo@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // 가장 가까운 ALIGNMENT(8)의 배수 리턴

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 내가 작성한 매크로(책 참고) */
#define WSIZE 4 // Word and header/footer size
#define DSIZE 8 // Double word size
#define CHUNKSIZE (1<<12) // heap 늘리는 최소 사이즈(4096byte -> 별 의미 없는듯)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// 할당할 블록의 사이즈(size)와 할당 여부를 넣으면 그걸 합쳐줌 -> header에 들어갈 값이 됨
#define PACK(size, alloc) ((size) | (alloc))

// p를 unsigned int형 포인터라 치고 해당 포인터 주소에 저장된 값을 불러온다.
// 헤더에 들어 있는 값 읽을 때 사용
#define GET(p) (*(unsigned int *)(p))

// p를 unsigned int형 포인터라 치고 해당 포인터 주소에 val을 저장
// 헤더에 값 넣을 때 사용
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 헤더를 가리키는 포인터 p에 저장된 값을 읽어 해당 블록의 사이즈, 할당 여부 리턴(bytes)
#define GET_SIZE(p) (GET(p) & ~0x7) // 사이즈는 4~32번째 비트에 저장돼 있다.
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp : 블록의 헤더 바로 뒤를 가리키는 포인터
// bp를 가지고 해당 블록의 header와 footer의 주소를 리턴해줌
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음, 이전 블록의 포인터 리턴
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 뒷 블록의 header에서 GET_SIZE
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 앞 블록의 footer에서 GET_SIZE


// heap_listp -> static global variable
static void *heap_listp = NULL; // heap의 시작점 가리킴
static void *start_bp = NULL; // 할당시켰던 마지막 bp(next_fit에 사용)

int mm_init(void);
void mm_free(void *bp);
void *mm_malloc(size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // mem_sbrk를 통해 힙 키우기가 성공하면 heap_listp에 old_brk값을 할당
    // start_of_heap과 prologue, epilogue 때문에 4 word인듯?
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1) { // 힙을 늘릴 수 없는 경우
        return -1;
    }
    PUT(heap_listp, 0); // start_of_heap (alignment를 위한 padding)
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // epilogue header
    heap_listp += (2*WSIZE); // 힙의 시작점 위치를 prologue header 뒤로 옮겨줌

    // CHUNKSIZE만큼 힙 크기를 늘려줌
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) { // 힙을 늘릴 수 없으면
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp; // block의 시작점(header 앞 / block pointer 인듯)
    size_t size;

    // alignment를 위해 words의 사이즈가 홀수면 1을 더해서 2의 배수로 맞춰주고 byte 크기에 맞도록 WSIZE를 곱해준다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // bp에 old_brk값이 들어감 새로 만들 블록의 시작점(헤더 뒤)
    if ((long)(bp = mem_sbrk(size)) == -1) { // extend가 불가능하면 NULL 리턴
        return NULL;
    }
    // 힙을 늘리면서 생긴 공간을 블록으로 만들어주고
    // (이전 힙의 epilogue, 새로 만든 힙의 끝-1 을 블록의 header, footer로 값을 넣어줌)
    // 힙의 맨 끝으로 epilogue의 header를 옮겨줌
    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // epilogue header 옮겨주기
    
    // 앞의 블록이 free 상태이면 앞과 합체
    return coalesce(bp); // 생성된 블록의 bp 리턴
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; // Adjusted block size, 할당된 블록의 크기
    size_t extend_size; // 맞는 블록이 없을 경우 늘릴 사이즈
    char *bp; // 블록이 시작하는 위치 포인터

    if (size == 0) { // size 0 요청은 무시
        return NULL;
    }
    
    if (size <= DSIZE) { // 요청한 size가 8보다 작으면 
        asize = 2*DSIZE; // header+footer = 8이므로 두 배 할당
    }
    else { // 요청한 사이즈(size)와 header+footer의 사이즈(DSIZE)와 여유 사이즈(DSIZE-1)를 고려해
    // DSIZE(8)의 배수(DSIZE*)만큼 할당하기 위한 식이 아래 식
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    // asize에 맞는 블록 찾기
    if ((bp = next_fit(asize)) != NULL) {
        place(bp, asize); // bp 블록을 쪼개고 할당해주기?
        return bp;
    }
    
    // 맞는 게 없다면
    extend_size = MAX(asize, CHUNKSIZE); // CHUNKSIZE와 asize 중에 큰 값으로 힙 확장
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) { // 키우려는 사이즈의 word 수만큼 힙 확장 시도
        return NULL; // 힙 확장 실패하면
    }
    place(bp, asize); // bp 블록에 쪼개고 할당해주기?
    return bp;
}

// 현재 힙에서 asize에 맞는 bp를 찾아서 리턴
// next fit : 탐색할 때 다음 종료 지점부터 탐색
static void *next_fit(size_t asize) {
    void *bp = (start_bp == NULL) ? heap_listp : start_bp;

    size_t block_size = GET_SIZE(HDRP(bp)); // 블록 사이즈
    size_t alloc = GET_ALLOC(HDRP(bp)); // 블록 할당 여부

    // 블록 사이즈가 1 이상(epilogue 사이즈가 0)이고, 블록이 할당되었거나 asize가 블록 사이즈보다 클 동안
    while (block_size && (alloc || (asize > block_size))) { 
        bp = NEXT_BLKP(bp);
        block_size = GET_SIZE(HDRP(bp));
        alloc = GET_ALLOC(HDRP(bp));
    }
    if (block_size) {
        return bp;
    }
    return NULL;
}

// bp 블록에 asize만큼 쪼개주고 할당상태로 바꿔주기
static void place(void *bp, size_t asize) {
    size_t old_size = GET_SIZE(HDRP(bp));

    // 원래의 block에 asize를 할당하고 또 한 개의 블록을 만들 수 있는 공간(2*DSIZE)이 나면
    if ((old_size - asize) >= 2*DSIZE) { 
        // 할당해줄 블록 header, footer 설정
        PUT(HDRP(bp), PACK(asize, 1)); 
        PUT(FTRP(bp), PACK(asize, 1));
        // 나머지 블록 header, footer 재설정
        PUT(HDRP(NEXT_BLKP(bp)), PACK(old_size-asize, 0)); 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(old_size-asize, 0));
    }
    else { // 원래 블록 전체를 할당해야 하는 경우
        PUT(HDRP(bp), PACK(old_size, 1)); 
        PUT(FTRP(bp), PACK(old_size, 1));
    }
    start_bp = NEXT_BLKP(bp);
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    // 블록의 header와 footer의 할당상태 0으로 바꿔줌
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp); // 이전 or 이후의 블록이 free라면 합체
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 이후 블록 할당 여부
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

    if (prev_alloc && next_alloc) { // case 1 - 앞, 뒤 블록 모두 이미 할당
        return bp;
    }
    else if (prev_alloc && !next_alloc) { // case 2 - 앞 할당, 뒤 free -> 뒤랑 합체
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // header의 값 업데이트
        PUT(FTRP(bp), PACK(size, 0)); // footer의 값 업데이트 -> 반드시 header-footer 순으로 업데이트 해야함(FTRP 함수에 HDRP가 쓰이기 떄문)
        // 원래 있던 footer랑 header는 처리 안해줌..? -> 아 그냥 쓰레기 값이 되는 구나(어차피 접근 불가)
    }
    else if (!prev_alloc && next_alloc) { // case 3 - 앞 free, 뒤 할당 -> 앞이랑 합체
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0)); // 현재 block의 footer 업데이트
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 block의 header 업데이트
        bp = PREV_BLKP(bp); // 앞이랑 합쳤으니까 bp 업데이트
    }
    else { // case 4 - 앞, 뒤 모두 합치는 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 block의 header 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 이후 block의 footer 업데이트
        bp = PREV_BLKP(bp);
    }
    start_bp = bp;
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    
    copySize = GET_SIZE(HDRP(bp));
    
    if (size < copySize)
        copySize = size;
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}