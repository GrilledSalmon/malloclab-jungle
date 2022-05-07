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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

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

int mm_init(void);
void mm_free(void *bp);
void *mm_malloc(size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);

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
    char *bp; // block의 시작점(header 앞)
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
    return coalesce(bp);
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














