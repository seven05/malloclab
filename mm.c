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
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 // word and header footer 사이즈를 byte로
#define DSIZE 8 // double word size를 byte로
#define CHUNKSIZE (1<<12) // heap을 늘릴 때 4kb 분량으로 늘림.

#define MAX(x,y) ((x)>(y) ? (x) : (y)) // x,y 중 큰 값을 가진다.

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), 헤더에서 써야하기 때문에 생성.
#define PACK(size,alloc) ((size)|(alloc)) // alloc : 가용여부 (ex.000) / size : block size를 의미 -> 이를 통합해서 header와 footer에 저장할 수 있는 값 리턴

// 메모리 주소 p위치에 words를 읽고 씀
#define GET(p) (*(unsigned int*)(p)) // 인자 p가 참조하는 워드를 읽어서 리턴. 즉, 헤더에 담긴 정보를 꺼낼 수 있음
#define PUT(p,val) (*(unsigned int*)(p)=(val)) // 인자 p가 가리키는 워드에 val을 저장

// 메모리 주소 p 위치에서 크기나 할당여부 확인
#define GET_SIZE(p) (GET(p) & ~0x7) // 0x7를 2진수에서 역수를 취하면 11111000이 됨. 이것을 GET(p)를 통해 가져온 헤더 정보에 and 연산을 하면 block size만 가져올 수 있음
#define GET_ALLOC(p) (GET(p) & 0x1) // 위의 케이스와 반대로 00000001을 and해주면 헤더에서 가용여부만 가져올 수 있음

// 블록의 bp를 받아서, header와 footer의 시작주소를 찾음 
#define HDRP(bp) ((char*)(bp) - WSIZE) // bp의 현재 주소에서 4byte(1워드)만큼 빼주면 헤더의 위치가 됨 (char*)인 이유는 (int*)일 경우에는 WSIZE로 인해 16이 반환되기 때문?
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더의 끝 지점부터 GET SIZE(블록의 사이즈)만큼 더한 다음 word를 2번빼는게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작 위치가 된다.


// 블록의 bp를 받아서, 이전 블록과 다음 블록의 주소를 계산 
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동 -> 그 다음 블록의 헤더 뒤로 감.)
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 그 전 블록의 bp위치로 이동.(이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동.)

// Explicit를 위한 매크로
#define PREV_FREE_POINTER(bp) (*(void **)(bp))
#define NEXT_FREE_POINTER(bp) (*(void **)(bp+WSIZE))

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);  
static void place(void *bp, size_t asize);  
static char *heap_listp;
static char *last_bp; // explicit 버전
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)  // 초기의 빈 heap 할당(mem_sbrk)  
        return -1;  
    PUT(heap_listp, 0); // Alignment padding 생성
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); // prologue header 생성
    PUT(heap_listp + (2*WSIZE), NULL); // prev
    PUT(heap_listp + (3*WSIZE), NULL); // next
    PUT(heap_listp + (4*WSIZE), PACK(DSIZE,1)); // prologue footer 생성
    PUT(heap_listp + (5*WSIZE), PACK(0,1)); // epilogue block header 생성
    heap_listp += (2*WSIZE); // prologue header와 footer 사이로 포인터를 옮김.

    // 빈 Heap을 CHUNKSIZE byte로 확장하고, 초기 가용 블록을 생성해줌 
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HDRP(bp), PACK(size, 0)); // free block header 생성
    PUT(FTRP(bp), PACK(size, 0)); // free block footer 생성
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // epilogue block을 뒤로 밈
    return coalesce(bp); // prev_block이 free상태라면 병합
}

// explicit버전 (LIFO)
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록이 할당되었는지 확인 : bp의 포인터를 통해 이전 블록을 찾고, 이 이전블록의 footer를 통해 할당 여부를 확인한다.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록이 할당되었는지 확인 : bp의 포인터를 통해 다음 블록을 찾고, 이 다음블록의 header를 통해 할당 여부를 확인한다.
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈 확인

    //case1 앞뒤 모두 할당
    if (prev_alloc && next_alloc){
        // 합쳐진 블록의 next prev 수정
        PUT(bp+WSIZE,NEXT_FREE_POINTER(heap_listp)); // 원래있던 루트의 next값을 나의 next값으로
        PUT(bp,NULL);   // 내 prev 값은 NULL 
        PUT(NEXT_FREE_POINTER(heap_listp),bp); // 다음 가용리스트 prev값을 현재 bp를 가르키도록함
        PUT(heap_listp + (3*WSIZE), bp);    // 루트의 next값을 현재bp로
        return bp;
    }
    //case2 앞만 할당
    else if (prev_alloc && !next_alloc){
        // 다음 블록 next prev 처리
        PUT(NEXT_FREE_POINTER(NEXT_BLKP(bp)),PREV_FREE_POINTER(NEXT_BLKP(bp))); //다음블록의 next블록의 prev에 다음블록의 prev값을넣어줌
        PUT(PREV_FREE_POINTER(NEXT_BLKP(bp)),NEXT_FREE_POINTER(NEXT_BLKP(bp))); //다음블록의 prev블록의 next값을 다음블록의 next값으로 바꿔줌
        PUT(NEXT_BLKP(bp),0); // 다음 블록의 prev 값 삭제
        PUT(NEXT_BLKP(bp)+WSIZE,0); //  next값 삭제
        // 합쳐진 블록의 next prev 수정
        PUT(bp+WSIZE,NEXT_FREE_POINTER(heap_listp)); // 루트의 next (다음 free블록) -> 나의 next
        PUT(NEXT_FREE_POINTER(heap_listp),bp);  // 다음 free 블록의 prev -> 나로
        PUT(heap_listp + (3*WSIZE), bp);    // 루트의 next가 나를 가르키도록
        // implicit때 쓰던 H,F 크기 수정
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 크기를 현재 size에 더해줘요.
        PUT(HDRP(bp), PACK(size, 0)); // header 갱신 (더 큰 크기로 PUT)
        PUT(FTRP(bp), PACK(size,0)); // footer 갱신
    }
    //case3 뒤만 할당
    else if (!prev_alloc && next_alloc){
        // 이전 블록 next prev 처리
        PUT(NEXT_FREE_POINTER(PREV_BLKP(bp)),PREV_FREE_POINTER(PREV_BLKP(bp))); //이전블록의 next블록의 prev에 다음블록의 prev값을넣어줌
        PUT(PREV_FREE_POINTER(PREV_BLKP(bp)),NEXT_FREE_POINTER(PREV_BLKP(bp))); //이전블록의 prev블록의 next값을 다음블록의 next값으로 바꿔줌
        PUT(NEXT_BLKP(bp)+WSIZE,NULL); // 내 prev값은 NULL
        // 합쳐진 블록의 next prev 수정
        PUT(PREV_BLKP(bp)+WSIZE,NEXT_FREE_POINTER(heap_listp)); // 루트의 next (다음 free블록) -> 나의 next
        PUT(NEXT_FREE_POINTER(heap_listp),PREV_BLKP(bp)); // 다음 free 블록의 prev -> 나로
        PUT(heap_listp + (3*WSIZE), PREV_BLKP(bp)); // 루트의 next가 나를 가르키도록
        // implicit때 쓰던 H,F 크기 수정
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 크기를 현재 size에 더해줘요.
        PUT(FTRP(bp), PACK(size,0)); // 현재 위치의 footer에 block size를 갱신해줌
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    //case4 앞뒤 모두 가용상태
    else{
        // 다음블록 처리
        PUT(NEXT_FREE_POINTER(NEXT_BLKP(bp)),PREV_FREE_POINTER(NEXT_BLKP(bp))); //다음블록의 next블록의 prev에 다음블록의 prev값을넣어줌
        PUT(PREV_FREE_POINTER(NEXT_BLKP(bp)),NEXT_FREE_POINTER(NEXT_BLKP(bp))); //다음블록의 prev블록의 next값을 다음블록의 next값으로 바꿔줌
        PUT(NEXT_BLKP(bp),0); // 다음 블록의 prev 값 삭제
        PUT(NEXT_BLKP(bp)+WSIZE,0); //  next값 삭제
        // 이전블록 처리
        PUT(NEXT_FREE_POINTER(PREV_BLKP(bp)),PREV_FREE_POINTER(PREV_BLKP(bp))); //이전블록의 next블록의 prev에 다음블록의 prev값을넣어줌
        PUT(PREV_FREE_POINTER(PREV_BLKP(bp)),NEXT_FREE_POINTER(PREV_BLKP(bp))); //이전블록의 prev블록의 next값을 다음블록의 next값으로 바꿔줌
        PUT(NEXT_BLKP(bp)+WSIZE,NULL); // 내 prev값은 NULL
        // 합쳐진 free 블록의 next prev 수정
        PUT(PREV_BLKP(bp)+WSIZE,NEXT_FREE_POINTER(heap_listp)); // 루트의 next (다음 free블록) -> 나의 next
        PUT(NEXT_FREE_POINTER(heap_listp),PREV_BLKP(bp)); // 다음 free 블록의 prev -> 나로
        PUT(heap_listp + (3*WSIZE), PREV_BLKP(bp)); // 루트의 next가 나를 가르키도록
        // implicit때 쓰던 H,F 크기 수정
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 및 다음 블록의 크기를 현재 size에 더해줘요.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    // last_bp = bp; // next_fit을 위해 필요한 부분
    return bp;
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    size_t asize; // block 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char *bp;

    // 유효하지않는 사이즈
    if (size == 0) return NULL;

    // 블록의 최소크기가 2*DSIZE (Header footer 때문)
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        // size보다 클 때, 블록이 가질 수 있는 크기 중, 최적회된 크기로 재조정
        asize = DSIZE * ((size + (DSIZE)+(DSIZE-1)) / DSIZE);
    }
    // fit에 맞는 free 리스트를 찾는다.
    if ((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }
    // fit에 맞는게 없는 경우, 메모리를 더 가져와 block을 위치시킴 
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

// best_fit으로 구현한 방법(할당할수있는 공간중에 가장 작은사이즈의 공간을 찾아서 할당)
static void *find_fit(size_t asize){
    char *bp = NULL;
    char *best_bp = NULL;
    size_t best_size = (size_t) -1; // size_t는 unsigned 타입이라 최대값으로 변함
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        // 헤더가 가용상태가 아니면서 사이즈를 만족해야 가용 가능
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            size_t diff_size = GET_SIZE(HDRP(bp)) - asize;
            if(diff_size < best_size){
                best_size = diff_size;
                best_bp = bp;
            }
        }
    }
    return best_bp;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 빈블록의 크기
    if ((csize-asize) >= (2*DSIZE)){    // 할당크기를 뺀뒤에 16바이트 이상남으면 분할
        PUT(HDRP(bp), PACK(asize,1));   // 일단 할당해야할 크기만큼 할당
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);             // 할당한 다음 블록으로
        PUT(HDRP(bp), PACK(csize-asize,0)); // 나머지 블록을 빈블록으로 선언
        PUT(FTRP(bp), PACK(csize-asize,0));
    }
    else {
        PUT(HDRP(bp), PACK(csize,1));   // 16바이트 이상 안남으면 그냥 할당
        PUT(FTRP(bp), PACK(csize,1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); // bp의 주소를 가지고 헤더에 접근하여(HDRP) -> block의 사이즈를 얻음(GET_SIZE)
    PUT(HDRP(ptr), PACK(size,0)); // header free -> 가용상태로 만들기
    PUT(FTRP(ptr), PACK(size,0)); // footer free -> 가용상태로 만들기
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;
    
    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //   return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // if (size < copySize)
    //   copySize = size;
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;
    if(size <= 0){  // 사용하는 메모리가 0이거나 음수면 메모리해제
        mm_free(ptr);
        return 0;
    }
    if(ptr == NULL){    //  ptr이 NULL이라는것은 할당된 메모리가 없다는 뜻이므로
        return mm_malloc(size); // 새로 할당해준다
    }
    void *newp = mm_malloc(size);   // 새로운 크기의 메모리블럭을 할당
    if(newp == NULL) {          // 할당 못받으면 NULL로 malloc이 반환
        return 0;           // 에러처리
    }
    size_t oldsize = GET_SIZE(HDRP(ptr));   //기존의 메모리 블럭 크기
    if(size < oldsize){             // 새로 요청한 크기가 기존보다 작으면
        oldsize = size;     // 데이터를 가져올때 요청한 크기만큼만 가져옴
    }
    memcpy(newp, ptr, oldsize); // 기존 블럭의 데이터를 새로운 블럭에다가 복사
    mm_free(ptr);   // 기존 블럭 메모리 할당 해제
    return newp;    // 새로 할당한 주소 반환
}














