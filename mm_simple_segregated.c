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

/* 매크로 */
#define WSIZE 4 // Word and header/footer size
#define DSIZE 8 // Double word size
#define CLASS_SIZE 20 // 나눌 클래스의 개수(적당히 큰 값으로..^^ 2^20이 대략 100만인데 나중에 줄여도 될듯)
#define CHUNKSIZE (1<<12) // heap 늘리는 최소 사이즈(4096byte -> 별 의미 없는듯)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// p를 unsigned int형 포인터라 치고 해당 포인터 주소에 저장된 값을 불러온다.
// 헤더에 들어 있는 값 읽을 때 사용
#define GET(p) (*(unsigned int *)(p))

// p를 unsigned int형 포인터라 치고 해당 포인터 주소에 val을 저장
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// bp : 블록의 succ 바로 뒤를 가리키는 포인터
// bp를 가지고 해당 블록의 successor의 주소를 리턴
#define SUCP(bp) ((char *)(bp) - WSIZE) // successor 위치 리턴

// successor에 저장된 값을 읽음
// 할당된 상태일 때 : 해당 블록의 클래스 리턴
// 할당되지 않은 상태일 때 : 링크드 리스트의 다음 블록 주소 리턴
#define GET_SUCC(bp) (*(int *)(SUCP(bp)))

// 만들 수 있는 최소한의 블록 사이즈(implicit이냐, explicit 등에 따라 수정)
// successor = 4이므로 payload가 들어갈 최소 공간(4)까지 DSIZE 할당(8의 배수로 align)
#define MIN_BLOCK_SIZE DSIZE // simple segregeted -> 페이로드 4 바이트

// heap_listp -> static global variable
// 이거 그냥 함수 안으로 넣어줘도 될 것 같기도~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
static void *heap_listp = NULL; // heap의 시작점 가리킴
static void *root_startp = NULL; // class별 root 포인터가 시작되는 지점

// class_num에 따른 root의 주소 리턴
#define ROOT_ADDR(class_num) (((class_num) * WSIZE) + (char *)(root_startp))
// class_num에 따른 root 포인터 리턴
#define ROOTP(class_num) GET(ROOT_ADDR(class_num))

/* class의 사이즈는 payload+padding영역 기준이다.(ex. 4-class의 블록 사이즈는 2^4 + WSIZE = 20) */



int mm_init(void);
int root_init(void);
void mm_free(void *bp);
void *mm_malloc(size_t size);
static void *extend_heap(size_t words);
// static void *coalesce(void *bp);
// static void *find_fit(size_t asize);
// static void place(void *bp, size_t asize);
static void linked_list_delete(void *bp);
static void insert_to_root(void *bp);
static void linked_list_connect(void *prev_bp, void *now_bp, void *next_bp);
static int get_class(int size);
static void allocate_block(void *bp, size_t class_num);
static void extend_linked_list(void * bp, size_t created_block_num, size_t class_num);
static void insert_to_class(void *bp, size_t class_num);




// heap 영역에 class의 root포인터를 저장할 공간을 할당
int root_init()
{
    // class 개수만큼 할당
    if ((root_startp = mem_sbrk(CLASS_SIZE*WSIZE)) == (void *) -1) {
        return -1;
    }
    for (int i=0; i<CLASS_SIZE; i++) {
        PUT(ROOT_ADDR(i), NULL); // 초기화
    }
}


// heap_listp 다른 데서 안 쓰면 전역변수로 말고 init 지역변수로 선언해주기
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    printf("---------------entered init!--------------- \n");
    char *bp = NULL;
    root_init(); // 힙 영역에 미리 class root들 초기화

    // mem_sbrk를 통해 힙 키우기가 성공하면 heap_listp에 old_brk값을 할당
    // start_of_heap과 prologue, epilogue 때문에 4 word인듯?
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1) { // 힙을 늘릴 수 없는 경우
        return -1;
    }
    PUT(heap_listp, 0); // start_of_heap (alignment를 위한 padding)
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3*WSIZE), NULL); // epilogue header -> 이거 있어야함 ㅋㅋㅋ(heap 확장 시 끝이 어딘지 알기 위해서) -> 아니 없어도 되는 것 같기도..?
    heap_listp += (2*WSIZE); // 힙의 시작점 위치를 prologue header 뒤로 옮겨줌

    // CHUNKSIZE만큼 힙 크기를 늘려줌 -----> 없어도 될듯?
    // if (bp = extend_heap(CHUNKSIZE/WSIZE) == NULL) { // 힙을 늘릴 수 없으면
    //     return -1;
    // }
    return 0;
}


// extend해서 생긴 블록은 여기서 pred, succ 설정해줄 필요 없음. 오히려 그러면 안됨.
static void *extend_heap(size_t words)
{   
    // printf("entered extend_heap! \n");
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
    // PUT(HDRP(bp), PACK(size, 0));

    // epilogue header 옮겨주기
    PUT(SUCP((char *)bp + size), NULL); // bp(확장된 힙 시작점, old_brk) + size == 힙의 끝지점
    
    return bp; // 생성된 블록의 bp 리턴
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   
    // printf("entered malloc! \n");
    
    if (size == 0) { // size 0 요청은 무시
        return NULL;
    }

    size_t class_num = get_class(size); // 할당될 블록의 클래스 번호
    size_t extend_size; // 맞는 블록이 없을 경우 늘릴 사이즈
    size_t created_block_num; // 생성된 블록 갯수
    char *bp; // 블록이 시작하는 위치 포인터
    
    // if (size <= WSIZE) { // 요청한 size가 4보다 작으면 
    //     asize = MIN_BLOCK_SIZE; // SUCC + 페이로드 4바이트 = 8바이트
    // }
    // else { // 요청한 사이즈(size)와 header+pred+succ+footer의 사이즈(2*DSIZE)와 여유 사이즈(DSIZE-1)를 고려해
    // // DSIZE(8)의 배수(DSIZE*)만큼 할당하기 위한 식이 아래 식
    //     asize = DSIZE * ((size + MIN_BLOCK_SIZE - 1) / DSIZE);
    // }

    // class에 블록이 있나 찾기
    if (bp = ROOTP(class_num) != NULL) {
        allocate_block(bp, class_num);
        return bp;
    }

    size = 1<<class_num; // 할당해야 하는 size를 class의 size로 바꿔줌
    
    // 할당해야 하는 블록의 사이즈가 CHUNKSIZE보다 작으면 블록의 갯수는 나눈 수만큼, 아니면 한 개만 할당
    created_block_num = (size <= CHUNKSIZE) ? CHUNKSIZE / size : 1;

    // printf("malloc extend_heap runned! with size : %d \n", size);
    // 맞는 게 없다면 
    extend_size = created_block_num * (WSIZE + size); // 블록 갯수 * 블록 사이즈
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) { // 키우려는 사이즈의 word 수만큼 힙 확장 시도
        return NULL; // 힙 확장 실패하면
    }
    
    // 확장된 영역을 쪼개고 링크드 리스트 연결
    extend_linked_list(bp, created_block_num, class_num);

    // bp 블록을 allocate
    allocate_block(bp, class_num);
        
    return bp;
}



// class_num에서 첫 번째 블록을 제거하고 할당한 블록의 succ에 기존 class_num을 넣어줌
// class_num의 root != NULL이 아니라는 가정
static void allocate_block(void *bp, size_t class_num)
{
    // 블록 제거(root가 succ 블록 가리키게 해주기)
    PUT(ROOT_ADDR(class_num), GET_SUCC(bp)); // class_num의 루트에 현재 bp가 가리키는 값 넣어줌
    PUT(SUCP(bp), class_num); // 할당된 블록의 successor에 자신의 클래스 번호 넣어주기
}



// 힙을 확장하며 생긴 영역을 분할하고 링크드 리스트에 추가
static void extend_linked_list(void * bp, size_t created_block_num, size_t class_num)
{
    size_t block_size = WSIZE + (1<<class_num);
    // root의 시작점으로 bp를 넣어줌
    PUT(ROOT_ADDR(class_num), bp);

    // 링크드 리스트 연결
    for (int i=0; i < created_block_num-1; i++) {
        PUT(SUCP(bp), (char *)bp + block_size); // 현재 bp의 succ에 다음 블록의 주소를 넣어줌
        bp = (char *)bp + block_size; // 다음 블록
    }
    PUT(SUCP(bp), NULL); // 마지막 블록의 succ은 NULL을 가리키도록
}



// // explicit check done
// // class_num에 따른 링크드 리스트에서 bp를 찾아서 리턴
// static void *find_fit(size_t class_num) {
//     // printf("entered find_fit!\n");
//     void *bp = root; // 탐색을 root에서 시작
    
//     // bp가 링크드 리스트의 끝에 도달(bp == NULL)하지 않고, 블록이 할당되었거나 asize가 블록 사이즈보다 클 동안
//     // printf("find_fit with %p, %p\n", bp, NEXT_ADDR(bp));
//     while (bp != NULL && (GET_ALLOC(HDRP(bp)) || (asize > GET_SIZE(HDRP(bp))))) { 
//         // printf("%p -> ", bp);
//         bp = NEXT_ADDR(bp); // 링크드 리스트의 다음 블록 주소
//     }
//     // printf("\n");
//     return bp;
// }

// // explicit check done
// // bp 블록의 앞을 asize만큼 쪼개주고 할당상태로 바꿔주기
// static void place(void *bp, size_t asize) {
//     // printf("entered place!\n");
//     size_t old_size = GET_SIZE(HDRP(bp));
    
//     // 원래의 block에 asize를 할당하고 또 한 개의 블록을 만들 수 있는 공간(3*DSIZE)이 나면
//     if ((old_size - asize) >= MIN_BLOCK_SIZE) { 
//         void *prev_bp = PREV_ADDR(bp);
//         void *next_bp = NEXT_ADDR(bp);
    
//         // 할당해줄 블록 header, footer 설정

//         PUT(HDRP(bp), PACK(asize, 1)); 
//         PUT(FTRP(bp), PACK(asize, 1));
    
//         // 나머지 블록 header, footer 재설정
//         bp = NEXT_BLKP(bp);
//         PUT(HDRP(bp), PACK(old_size-asize, 0)); 
//         PUT(FTRP(bp), PACK(old_size-asize, 0));
    
//         // 나머지 블록과 기존 링크드 리스트 이웃 블록들과 재연결
//         linked_list_connect(prev_bp, bp, next_bp);
//     }
//     else { // 원래 블록 전체를 할당해야 하는 경우
//         linked_list_delete(bp); // 현재 블록을 링크드 리스트에서 삭제
//         PUT(HDRP(bp), PACK(old_size, 1)); 
//         PUT(FTRP(bp), PACK(old_size, 1));
//     }
// }

// explicit check done
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // printf("entered free! \n");
    size_t class_num = GET_SUCC(bp);

    PUT(SUCP(bp), ROOTP(class_num)); // 원래 root가 가리키던 블록을 bp의 succ이 가리키도록
    PUT(ROOT_ADDR(class_num), bp); // class의 root가 bp를 가리키도록

    // // 블록의 header와 footer의 할당상태 0으로 바꿔줌
    // PUT(HDRP(bp), PACK(size, 0));
    // PUT(FTRP(bp), PACK(size, 0));
    // coalesce(bp); // 이전 or 이후의 블록이 free라면 합체
}


// // free된 블록을 원래 class로 다시 넣어줌
// static void insert_to_class(void *bp, size_t class_num) 
// {  
//     PUT(SUCP(bp), ROOTP(class_num)); // 원래 root가 가리키던 블록을 bp의 succ이 가리키도록
//     PUT(ROOT_ADDR(class_num), bp); // class의 root가 bp를 가리키도록
// }

// // explicit check done
// // coalesce로 들어오는 bp는 pred, succ 설정이 되어 있지 않아야 한다.
// static void *coalesce(void *bp)
// {   
//     // printf("entered coalesce!\n");
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 여부
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 이후 블록 할당 여부
//     size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

//     if (prev_alloc && next_alloc) { // case 1 - 앞, 뒤 블록 모두 이미 할당
//         // 패스
//     }
//     else if (prev_alloc && !next_alloc) { // case 2 - 앞 할당, 뒤 free -> 뒤랑 합체
//         linked_list_delete(NEXT_BLKP(bp));
//         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//         PUT(HDRP(bp), PACK(size, 0)); // header의 값 업데이트
//         PUT(FTRP(bp), PACK(size, 0)); // footer의 값 업데이트 -> 반드시 header-footer 순으로 업데이트 해야함(FTRP 함수에 HDRP가 쓰이기 떄문)
//         // 원래 있던 footer랑 header는 처리 안해줌..? -> 아 그냥 쓰레기 값이 되는 구나(어차피 접근 불가)
//     }
//     else if (!prev_alloc && next_alloc) { // case 3 - 앞 free, 뒤 할당 -> 앞이랑 합체
//         linked_list_delete(PREV_BLKP(bp));
//         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//         PUT(FTRP(bp), PACK(size, 0)); // 현재 block의 footer 업데이트
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 block의 header 업데이트
//         bp = PREV_BLKP(bp); // 앞이랑 합쳤으니까 bp 업데이트
//     }
//     else { // case 4 - 앞, 뒤 모두 합치는 경우
//         linked_list_delete(NEXT_BLKP(bp));
//         linked_list_delete(PREV_BLKP(bp));
//         size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 block의 header 업데이트
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 이후 block의 footer 업데이트
//         bp = PREV_BLKP(bp);
//     }

//     insert_to_root(bp); // bp를 링크드 리스트의 root로 넣어줌
//     return bp;
// }

// explicit check done
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) // bp를 size가 되도록 다시 allocate
{
    // printf("entered realloc! \n");
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

// // bp블록을 링크드 리스트에서 삭제
// static void linked_list_delete(void *bp)
// {   
//     // printf("entered delete! \n");
//     void *prev_bp = PREV_ADDR(bp); // 링크드리스트에서 bp의 이전 블록
//     void *next_bp = NEXT_ADDR(bp); // bp의 이후 블록

//     // 링크드 리스트에 bp만 있었던 경우 -> 링크드 리스트 비워주기
//     if ((prev_bp == NULL) && (next_bp == NULL)) { 
//         root = NULL;
//     }
//     // bp가 root와 연결되어 있었던 경우 -> next_bp를 root와 연결
//     else if (prev_bp == NULL) { 
//         root = next_bp;
//         PUT(PRDP(next_bp), NULL);
//     }
//     // bp가 링크드 리스트의 맨 끝이었던 경우 -> prev_bp를 맨 끝으로
//     else if (next_bp == NULL) {
//         PUT(SUCP(prev_bp), NULL);
//     }
//     // bp의 앞, 뒤 블록이 모두 있었던 경우 -> prev_bp, next_bp를 서로 연결
//     else {
//         PUT(SUCP(prev_bp), next_bp);
//         PUT(PRDP(next_bp), prev_bp);
//     }
// }



// // bp를 링크드 리스트의 root로 넣어줌
// static void insert_to_root(void *bp) {
//     // printf("insert_to_root %p %p \n", bp, root);
//     // bp != root라는 가정
//     if (root != NULL) {
//         PUT(PRDP(root), bp);
//     }
//     PUT(PRDP(bp), NULL);
//     PUT(SUCP(bp), root);
//     root = bp;

// }



// // 링크드 리스트에서 prev_bp와 now_bp와 next_bp를 연결
// static void linked_list_connect(void *prev_bp, void *now_bp, void *next_bp) {
//     // printf("entered connect! %p %p %p\n", prev_bp, now_bp, next_bp);
//     if ((prev_bp == NULL) && (next_bp == NULL)) {
//         root = now_bp;
//     }
//     else if (prev_bp == NULL) {
//         root = now_bp;
//         PUT(PRDP(next_bp), now_bp);    
//     }
//     else if (next_bp == NULL) {
//         PUT(SUCP(prev_bp), now_bp);    
//     }
//     else {
//         PUT(SUCP(prev_bp), now_bp);
//         PUT(PRDP(next_bp), now_bp);    
//     }
//     PUT(PRDP(now_bp), prev_bp);
//     PUT(SUCP(now_bp), next_bp);
// }


// /* class의 사이즈는 payload+padding영역 기준이다.(ex. 4-class의 블록 사이즈는 2^4 + WSIZE = 20) */
// // size만큼 할당받고자 할 때 배정받을 최소 class 리턴
// // 0~CLASS_SIZE-1 의 class가 대상
// static int get_class(int size) {
//     size_t class_num = 0;
//     while (size > (1<<class_num)) {
//         class_num++;
//     }
//     if (class_num < 2){
//         return 2; // 최소 페이로드 크기가 WSIZE(4바이트이기 때문)
//     }

//     if (class_num >= CLASS_SIZE) { // 나중에 에러 안 뜨면 지워주기
//         printf("ERROR -- 너무 큰 사이즈가 들어와 클래스에 할당할 수 없습니다.\n");
//         return NULL;
//     }

//     return class_num;
// }