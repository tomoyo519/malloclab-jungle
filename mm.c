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
    "5Team",
    /* First member's full name */
    "Dahee Cheong",
    /* First member's email address */
    "vanessa.cheong1@gmail.com",
    /* Second member's full name (leave blank if none) */
    "Hoyoung Jang",
    /* Second member's email address (leave blank if none) */
    "jisung@gmail.com"
};


// 할당은 되어있으나 사용은 하지않는..
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 초기 가용 리스트 만들기

/* 
 * mm_init - initialize the malloc package.
 */
//초기 힙영역을 할당한다.

// 기본 상수 정의
#define WSIZE 4 // word size
#define DSIZE 8 // double word size
#define CHUNKSIZE (1<<12) // 힙 확장을 위한 기본 크기 ( = 초기 빈 블록의 크기) 이 안에 에필 프롤로그가 들어가는것. 1000000000000;

//  힙에 접근/순회하는데 사용할 매크로
#define MAX(x,y) ((x) > (y) ? (x):(y))
// 가용리스트에 접근하고 방문하는 작은 매크로 정의

// or 연산자를 하면서 1로 바꿔주는것.
//비트 Or 연산 :할당정보랑, 사이즈정보를 합친다
// 사이즈값에 할당비트를 넣는느낌.. 사이즈랑 할당비트를 통합하는것
#define PACK(size, alloc) ((size) | (alloc)) // size와 할당 비트를 결합, header와 footer에 저장할값

//비트 and 연산자는 대응되는 두 비트가 모두 1일때만



#define GET(p) (*(unsigned int *)(p)) // p가 참조하는 워드 반환 (포인터라서 직접 역참조 불가능 ->타입캐스팅 )
#define PUT(p,val) (*(unsigned int *)(p) = (val)) // p에 val 저장

// 각 주소 p에 있는 헤더 또는 푸터의 사이즈와 할당 비트를 리턴한다.
#define GET_SIZE(p) (GET(p) & ~0x7) // 사이즈 (~0x7 : ...1000, '&'연산으로 뒤에 세자리 없어짐) 16진수인 0x7을 2진수로 바꾸면 1111이라 ~연산자를 사용해서 뒷자리를 전부 0으로 바꾸는것임
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 상태를 표시하기 위함

// 각각 헤더와 풋터를 가리키는 포인터를 리턴한다.
//블록 크기는 지정이 아니다.

#define HDRP(bp) ((char *)(bp) - WSIZE) // header 포인터 
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블럭포인터 + 지금 포인터 가 가리키는 블럭의 크기
// 헤더의 정보를 변경했다면 변경된 위치의 footer 가 반환됨
// 다음 블록의 블록 포인터, 이전 블록의 블록 포인터
// 한 블록의 크기가 2워드이다. = 8바이트

//bp는 페이로드의 시작점을 가리킨다.
//헤더랑 푸터는 사이즈가 1워드씩, 4바이트씩.
// 한개의 블록 사이즈는 정해져있지 않는다.
#define NEXT_BLKP(bp) ((char *) (bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 다음 블록의 페이로드 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 이전블록의 페이로드 포인터

static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
int mm_init(void);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
void mm_free(void *ptr);
static void *coalesce(void *bp);
void *mm_realloc(void *ptr, size_t size);
static void *last_bp; // 기존값을 유지해야 하므로 static 으로 선언.
static void *heap_listp;
//last_bp가 업데이트 되는 경우 : 첫번쨰 init => last_bp = heap_listp로 초기화
// place 되었을 때 bp 변경
// coalesce로 블록 합치는 과정에서 앞블록과 합쳐질 경우 bp 변경됨

int mm_init(void)
{
    // 메모리 시스템에서 4워드를 가져와서 빈 가용 리스트를 만들 수 있도록 이들을 초기화 한다.
    //시스템콜 = mem_sbrk
    // char *heap_listp;
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){ // 할당이 안된 경우,
        return -1;
    }

    //힙영역에서 시작 = 프롤로그 
    // 끝 = 에필로그
    PUT(heap_listp, 0); // 정렬패딩  : 맨 앞자리에 0을 집어 넣은것임.
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); // 프롤로그 header 할당되었다는 표시만 하는것.
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); // 프롤로그 footer = 헤더정보
    PUT(heap_listp + (3 *WSIZE), PACK(0,1)); // 에필로그 header :  사이즈가 0이라고 넣는것. 더이상 데이터가 없다. 프로그램이 할당한 마지막 블록 의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄.
    //next-fit 구현
   
    //그 다음의 페이로드를 가리킨다.
    heap_listp += (2*WSIZE);
    // 그 이후에 extend_heap 함수를 호출해서 힙을 CHUNKSIZE 바이트로 확장하고 초기 가용 블록을 생성한다. 
    // 여기까지 할당기는 초기화를 완료하고, 어플리케이션으로부터 할당과 반환 요청을 받을 준비를 완료하였다.

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    //last_bp 초기화
    last_bp = heap_listp;
    return 0;
}


static void *extend_heap(size_t words)
{
    char *bp;

    // 더블 워드 정렬 유지
    // size: 확장할 크기
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해서 곱함)

    if ((long)(bp = mem_sbrk(size)) == -1) // 자리 없을 때 힙 확장
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새 빈 블록 헤더 초기화
    PUT(FTRP(bp), PACK(size, 0));         // 새 빈 블록 푸터 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 블록 헤더 초기화

    return coalesce(bp); // 병합 후 coalesce 함수에서 리턴된 블록 포인터 반환
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
    size_t asize; // 조정된 블록 사이즈
    size_t extendsize; // 적절한 자리가 없을 경우, heap 의 공간을 늘리는 양. 확장할 사이즈
    char *bp;
    // 잘못된 요청 분기
    if (size ==0){
        return NULL;
    }
    // adjust block size to include overhead and alignment reqs;
    // 사이즈 조정
    if(size <=DSIZE){  // 8바이트 이하이면, 왜 8바이트 이하면 블록의 최소크기가 8바이트이기 때문에
        asize = 2*DSIZE; // 최소 블록크기 16바이트 할당( 헤더 4바이트, 푸터 4바이트, 저장공간 8바이트) 

    }else{
        asize = DSIZE *  ((size + (DSIZE) +(DSIZE-1)) / DSIZE); //8배수로 올림처리
        // moduler 연산
    }
    // 가용 블록 검색
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize); // 할당
        last_bp = bp;
        return bp; // 새로 할당된 블록의 포인터 리턴
    }
    // 적합한 블록이 없을경우, 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    last_bp = bp;
    return bp;
}


//데이터를 할당할 가용 블록의 bp 와 배치 용량 할당
static void place(void *bp, size_t asize){
    // free block 처음에 requested block을 두어야 한다....
    // 나머지 크기가 최소블록 크기와 동일하거나 초과할 경우에만 분할해야 한다.
    //블록의 최소 크기 = 16바이트

    //말록에게 이만크 자리를 줘, 말록이 줬음, csize = 말록이 준 할당되지않은 블록
    // 현재 사이즈가 할당한 사이즈보다 당연히 클텐데, 그 차이가 더블워드 *2 이상이다?
    // 헤더푸터가 합쳐서 8바이트니까 필요한 만큼 할당하고, 그 이후 공간은 빈 공간으로 남기기. 

    size_t csize = GET_SIZE(HDRP(bp));
    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1)); // 헤더에 할당할 사이즈 업데이트
        PUT(FTRP(bp), PACK(asize, 1)); // 푸터에 할당할 사이즈 업데이트
        bp = NEXT_BLKP(bp); // bp를 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 할당하고 남은 크기만큼 가용 공간 남기기, 헤더에 사이즈 업데이트 하기
        PUT(FTRP(bp), PACK(csize-asize, 0)); // 풋터에 사이즈 업데이트
        //하니면 현재 블록 크기만큼 할당
    } else{
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *find_fit(size_t asize)

//처음부터 끝까지 탐색 = 퍼스트핏


// {
//     void *bp = mem_heap_lo() + 2 * WSIZE; // 첫번째 블록(주소: 힙의 첫 부분 + 8bytes)부터 탐색 시작
//     while (GET_SIZE(HDRP(bp)) > 0)
//     {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용 상태이고, 사이즈가 적합하면
//             return bp;                                             // 해당 블록 포인터 리턴
//         bp = NEXT_BLKP(bp);                                        // 조건에 맞지 않으면 다음 블록으로 이동해서 탐색을 이어감
//     }
//     return NULL;
// }

// next fit ==할당한 지점을 포인터로 따로 저장을 해두고,그 다음부터를 찾는것 끝까지 갓는데 자리가업서..
//근데 기존에 있던것중 프리가 된게 있을 수 있으니, 처음부터 저장했던 포인터까지 다시탐색
{
    //탐색을 하고 할당을 한 뒤에
  //next-fit 포인터에서 탐색 시작
  void *bp;
  //last_bp 이후에
  for(bp = last_bp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){
    if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))){
        return bp;
    }
  }
  //last_bp 부터 탐색햿는데 못찾았을 경우는 처음부터 탐색한다.
//   printf("%p", heap_listp);
  for(bp = heap_listp; HDRP(bp)!=HDRP(last_bp); bp = NEXT_BLKP(bp)){
    if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
        return bp;
    }
  }
//   for(bp = last_bp;)
return NULL;
}

// {
//     void *bp;
//     void *best_fit = NULL;

//     for(bp = heap_listp;  )
// }


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size  = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    coalesce(ptr);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 사이즈

    if(prev_alloc && next_alloc){ //모두 할당 된 경우 - case1
        return bp; 
    }
    else if(prev_alloc && !next_alloc){ // 다음 블록만 빈 경우 - case2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더의 사이즈
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size,0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정 했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if(!prev_alloc && next_alloc){ // 전 블록만 빈 경우 - case3
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
        PUT(FTRP(bp), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp); // 이전 블록의 시작점으로 포인터 변경
    }
    else{ // 이전블록과 다음 블록 모두 빈 경우 - case4
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp); // 이전 블록의 시작점으로 포인터 변경

    }
    last_bp = bp;
    return bp; // 병합된 블록의 포인터 변환;

}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
//  기존에 할당된 메모리 블록의 크기 변경
// args = '기존 메모리 블록의 포인터', '새로운 크기'
void *mm_realloc(void *ptr, size_t size)
{
    // 예외처리
    if(ptr == NULL){// 포인터가 NULL 인 경우 할당만 수행
        return mm_malloc(size);
    }
    if (size <= 0){
        mm_free(ptr);
        return 0;
    }
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL; // 할당 실패

    //   데이터 복사
    // 코드변경
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize) // 기존 사이즈가, 새크기보다 더크면
      copySize = size; //size로 크기 변경
      // 기본 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사

    memcpy(newptr, oldptr, copySize); // 새 블록으로 데이터 복사
    // 기존 블록 반환
    mm_free(oldptr);
    return newptr;
}