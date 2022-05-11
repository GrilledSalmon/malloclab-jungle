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


/*  Segregated Free List의 Simple Segregated Storage 방식으로 구현한 malloc입니다.
 * 시험의 test case는 통과했지만, 과제의 test case는 5번 케이스의 'ran out of memory'로 통과하지 못하였습니다. 
 * test case of test - Perf index = 36 (util) + 40 (thru) = 76/100
 */

/* class의 사이즈는 successor까지 포함한 것을 기준으로 한다.
    (ex. 4-class의 블록 사이즈는 2^4 = 16이며, payload의 사이즈는 12가 된다.) */

/* Macro & Static Variable*/
#define WSIZE 4 // Word and size
#define DSIZE 8 // Double word size (alignment 기준)
#define CLASS_SIZE 3*DSIZE // 클래스의 개수(적당히 큰 값으로 + alignment를 위해 8의 배수로)
// ( -> 첫 번째 bp의 succ가 class의 마지막 root를 침범하기 때문에 실제로 사용할 수 있는 class의 갯수는 CLASS_SIZE-1이다.)
#define CHUNKSIZE (1<<12) // heap 늘리는 최소 사이즈(4096byte -> 별 의미 없는듯)

// p를 unsigned int형 포인터라 치고 해당 포인터 주소에 저장된 값을 불러온다.
// 헤더에 들어 있는 값 읽을 때 사용
#define GET(p) (*(unsigned int *)(p))

// p를 unsigned int형 포인터라 치고 해당 포인터 주소에 val을 저장
#define PUT(p, val) (*(unsigned int *)(p) = (int)(val))

// bp : 블록의 succ 바로 뒤를 가리키는 포인터
// bp를 가지고 해당 블록의 successor의 주소를 리턴
#define SUCP(bp) ((char *)(bp) - WSIZE) // successor 위치 리턴

// successor에 저장된 값을 읽음
// 할당된 상태일 때 : 해당 블록의 클래스 리턴
// 할당되지 않은 상태일 때 : 링크드 리스트의 다음 블록 주소 리턴
#define GET_SUCC(bp) (*(int *)(SUCP(bp)))

// 만들 수 있는 최소한의 블록 사이즈(implicit이냐, explicit 등에 따라 수정)
// successor = 4이므로 payload가 들어갈 최소 공간(4)까지 DSIZE 할당(8의 배수로 align)
#define MIN_BLOCK_SIZE DSIZE // simple segregeted -> payload = 4 바이트


// class별 root 포인터가 시작되는 지점
static void *root_startp = NULL; 

// class_num에 따른 root의 주소 리턴
#define ROOT_ADDR(class_num) (((class_num) * WSIZE) + (char *)(root_startp))
// class_num에 따른 root 포인터 리턴
#define ROOTP(class_num) (void *)GET(ROOT_ADDR(class_num))



/* functions */
int mm_init(void);
void mm_free(void *bp);
void *mm_malloc(size_t size);
static void *extend_heap(size_t words);
static int get_class(int size);
static void allocate_block(void *bp, size_t class_num);
static void extend_linked_list(void * bp, size_t created_block_num, size_t class_num);



/* 
 * mm_init - initialize the malloc package.
 */
// heap 영역에 class의 root포인터를 저장할 공간을 할당
int mm_init(void)
{
    // class 개수만큼 할당
    if ((root_startp = mem_sbrk(CLASS_SIZE*WSIZE)) == (void *) -1) {
        return -1;
    }
    for (int i=0; i<CLASS_SIZE; i++) {
        PUT(ROOT_ADDR(i), NULL); // 초기화
    }

    return 0;
}



// heap의 크기를 words에 alignment를 적용해서 늘려줌
static void *extend_heap(size_t words)
{   
    char *bp; // block의 시작점
    size_t size;

    // alignment를 위해 words의 사이즈가 홀수면 1을 더해서 2의 배수로 맞춰주고 byte 크기에 맞도록 WSIZE를 곱해준다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // bp에 old_brk값이 들어감 새로 만들 블록의 시작점(헤더 뒤)
    if ((long)(bp = mem_sbrk(size)) == -1) { // extend가 불가능하면 NULL 리턴
        return NULL;
    }
    
    return bp; // 생성된 블록의 bp 리턴
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{       
    if (size == 0) { // size 0 요청은 무시
        return NULL;
    }

    size_t class_num = get_class(size); // 할당될 블록의 클래스 번호
    size_t extend_size; // 맞는 블록이 없을 경우 늘릴 사이즈
    size_t created_block_num; // 생성된 블록 갯수
    char *bp; // 블록이 시작하는 위치 포인터

    bp = ROOTP(class_num);
    if (bp != NULL) {
        // allocate_block(bp, temp_class_num);
        allocate_block(bp, class_num);
        return bp;
    }

    size = 1<<class_num; // 할당해야 하는 size를 class의 size로 바꿔줌
    
    // 할당해야 하는 블록의 사이즈가 CHUNKSIZE보다 작으면 블록의 갯수는 나눈 수만큼, 아니면 한 개만 할당
    created_block_num = (size <= CHUNKSIZE) ? CHUNKSIZE / size : 1;

    extend_size = created_block_num * size; // 블록 갯수 * 블록 사이즈
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) { // 키우려는 사이즈의 word 수만큼 힙 확장 시도
        return NULL; // 힙 확장 실패하면
    }
    
    // 확장된 영역을 클래스 크기에 맞게 쪼개고 링크드 리스트 연결
    extend_linked_list(bp, created_block_num, class_num);

    // bp 블록을 allocate
    allocate_block(bp, class_num);
    
    return bp;
}



// class_num에서 첫 번째 블록을 제거하고 할당한 블록의 succ에 기존 class_num을 넣어줌
// (note)class_num의 root != NULL이 아니라는 가정을 다른 함수에서 지켜줘야 함
static void allocate_block(void *bp, size_t class_num)
{
    // 블록 제거(root가 succ 블록 가리키게 해주기)
    PUT(ROOT_ADDR(class_num), GET_SUCC(bp)); // class_num의 루트에 현재 bp가 가리키는 값 넣어줌
    PUT(SUCP(bp), class_num); // 할당된 블록의 successor에 자신의 클래스 번호 넣어주기
}



// 힙을 확장하며 생긴 영역을 분할하고 링크드 리스트에 추가
static void extend_linked_list(void * bp, size_t created_block_num, size_t class_num)
{
    size_t block_size = 1<<class_num;
    
    // root의 시작점으로 bp를 넣어줌
    PUT(ROOT_ADDR(class_num), bp);

    // 링크드 리스트 연결
    for (int i=0; i < created_block_num-1; i++) {
        PUT(SUCP(bp), (char *)bp + block_size); // 현재 bp의 succ에 다음 블록의 주소를 넣어줌
        bp = (char *)bp + block_size; // 다음 블록
    }
    PUT(SUCP(bp), NULL); // 마지막 블록의 succ은 NULL을 가리키도록
}



/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t class_num = GET_SUCC(bp);

    PUT(SUCP(bp), ROOTP(class_num)); // 원래 root가 가리키던 블록을 bp의 succ이 가리키도록
    PUT(ROOT_ADDR(class_num), bp); // class의 root가 bp를 가리키도록
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) // bp를 size가 되도록 다시 allocate
{
    void *oldptr = bp;
    void *newptr = NULL;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    
    copySize = 1 << (GET_SUCC(bp));
    
    if (size < copySize)
        copySize = size;
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    
    return newptr;
}



/* class의 사이즈는 successor까지 포함한 것을 기준으로 한다.
    (ex. 4-class의 블록 사이즈는 2^4 = 16이며, payload의 사이즈는 12가 된다.) */

// size만큼 할당받고자 할 때 배정받을 최소 class 리턴
// 0~CLASS_SIZE-1 의 class가 대상
static int get_class(int size)
{
    size_t class_num = 3;
    while (size + WSIZE > (1<<class_num)) {
        class_num++;
    }

    return class_num;
}