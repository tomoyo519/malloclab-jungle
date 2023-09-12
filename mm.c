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
    "Dahee Cheong",
    /* First member's email address */
    "vanessa.cheong1@gmail.com",
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

// 초기 가용 리스트 만들기

/* 
 * mm_init - initialize the malloc package.
 */
//초기 힙영역을 할당한다.

// 기본 상수 정의
#define WSIZE 4 // word size
#define DSIZE 8 // double word size
#define CHUNKSIZE (1<<12) // 힙 확장을 위한 기본 크기 ( = 초기 빈 블록의 크기)

//  힙에 접근/순회하는데 사용할 매크로
#define MAX(x,y) ((x) > (y) ? (x):(y))
// 가용리스트에 접근하고 방문하는 작은 매크로 정의
// alloc = 0아니면 1 ; 헤더에 사이즈가 들어감. 내가 이 주소를 할당할거야, 팩 지금 사이즈에 1을 주면 된다. 
// or 연산자를 하면서 1로 바꿔주는것.
#define PACK(size, alloc) ((size) | (alloc)) // size와 할당 비트를 결합, header와 footer에 저장할값

#define GET(p) (*(unsigned int *)(p)) // p가 참조하는 워드 반환 (포인터라서 직접 역참조 불가능 ->타입캐스팅 )
#define PUT(p,val) (*(unsigned int *)(p) = (val)) // p에 val 저장

// 각 주소 p에 있는 헤더 또는 푸터의 사이즈와 할당 비트를 리턴한다.
#define GET_SIZE(p) (GET(p) & ~0x7) // 사이즈 (~0x7 : ...11111000, '&'연산으로 뒤에 세자리 없어짐) 16진수인 0x7을 2진수로 바꾸면 1111이라 ~연산자를 사용해서 뒷자리를 전부 0으로 바꾸는것임
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 상태

// 각각 헤더와 풋터를 가리키는 포인터를 리턴한다.
#define HDRP(bp) ((char *)(bp) - WSIZE) // header 포인터
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer 포인터(헤더의 정보를 참조해서 가져오기 때문에, 
//헤더의 정보를 변경했다면 변경된 위치의 footer 가 반환됨
//ㅡ다음 블록의 블록 포인터, 이전 블록의 블록 포인터
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 포인터
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소


static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
int mm_init(void);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
void mm_free(void *ptr);
static void *coalesce(void *bp);
void *mm_realloc(void *ptr, size_t size);
static char *free_listp;

static void splice_free_block(void *bp); // 가용 리스트에서 제거
static void add_free_block(void *bp);    // 가용 리스트에 추가

int mm_init(void)
{
      
    // 메모리 시스템에서 4워드를 가져와서 빈 가용 리스트를 만들 수 있도록 이들을 초기화 한다.
   if ((free_listp = mem_sbrk(8 * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, free_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(free_listp, 0);                                // 정렬 패딩
    PUT(free_listp + (1 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Header
    PUT(free_listp + (2 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Footer
    PUT(free_listp + (3 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 헤더
    PUT(free_listp + (4 * WSIZE), NULL);               // 이전 가용 블록의 주소
    PUT(free_listp + (5 * WSIZE), NULL);               // 다음 가용 블록의 주소
    PUT(free_listp + (6 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 푸터
    PUT(free_listp + (7 * WSIZE), PACK(0, 1));         // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄

    free_listp += (4 * WSIZE); // 첫번째 가용 블록의 bp

    // 힙을 CHUNKSIZE bytes로 확장
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

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
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize; // 조정된 블록 사이즈
    size_t extendsize; // 적절한 자리가 없을 경우, heap 의 공간을 늘리는 양. 확장할 사이즈
    char *bp;
    // 잘못된 요청 분기
    if (size ==0){
        return NULL;
    }
    // adjust block size to include overhead and alignment reqs;
    // 사이즈 조정
    if(size <=DSIZE){  // 8바이트 이하이면, ??? 왜 8바이트 이하면 ???
        asize = 2*DSIZE; // 최소 블록크기 16바이트 할당( 헤더 4바이트, 푸터 4바이트, 저장공간 8바이트) ??? 왜 이사이즈로 ?

    }else{
        asize = DSIZE *  ((size + (DSIZE) +(DSIZE-1)) / DSIZE); //8배수로 올림처리
        // ??? 이 코드가 어떻게 8배수로 올림 처리가 되는거지 ?
    }
    //  search the free list for a fit
    // 가용 블록 검색
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize); // 할당
        return bp; // 새로 할당된 블록의 포인터 리턴
    }

    // 적합한 블록이 없을경우, 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

static void place(void *bp, size_t asize)
{
    splice_free_block(bp); // free_list에서 해당 블록 제거

    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        add_free_block(NEXT_BLKP(bp)); // 남은 블록을 free_list에 추가
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void *find_fit(size_t asize)
{
    void *bp = free_listp;
    while (bp != NULL) // 다음 가용 블럭이 있는 동안 반복
    {
        if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
            return bp;
        bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
    }
    return NULL;
}

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

static void *coalesce(void *bp)
{

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc) // 모두 할당된 경우
    {
        add_free_block(bp); // free_list에 추가
        return bp;          // 블록의 포인터 반환
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        splice_free_block(NEXT_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        splice_free_block(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    add_free_block(bp); // 현재 병합한 가용 블록을 free_list에 추가
    return bp;          // 병합한 가용 블록의 포인터 반환
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
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize) // 기존 사이즈가, 새크기보다 더크면
      copySize = size; //size로 크기 변경
      // 기본 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사

    memcpy(newptr, oldptr, copySize); // 새 블록으로 데이터 복사
    // 기존 블록 반환
    mm_free(oldptr);
    return newptr;
}


static void splice_free_block(void *bp)
{
    if (bp == free_listp) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        free_listp = GET_SUCC(free_listp); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

// 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    GET_SUCC(bp) = free_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (free_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(free_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    free_listp = bp;               // 루트를 현재 블록으로 변경
}


