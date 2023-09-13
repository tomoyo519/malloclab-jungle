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
#define WSIZE 4 // word size: 4bytes
#define DSIZE 8 // double word size
#define CHUNKSIZE (1<<12) // 힙 확장을 위한 기본 크기 ( = 초기 빈 블록의 크기) 2^12 = 4096
// 페이징 개념 운영체제가 처리하는 양
#define PAGE_REQUEST_SIZE (3)

// for segregated List

#define SEGREGATE_SIZE (12) // segregated list의 class 갯수

//  힙에 접근/순회하는데 사용할 매크로
#define MAX(x,y) ((x) > (y) ? (x):(y))
// 가용리스트에 접근하고 방문하는 작은 매크로 정의
// alloc = 0아니면 1 ; 헤더에 사이즈가 들어감. 내가 이 주소를 할당할거야, 팩 지금 사이즈에 1을 주면 된다. 
// or 연산자를 하면서 1로 바꿔주는것.
#define PACK(size, alloc) ((size) | (alloc)) // size와 할당 비트를 결합, header와 footer에 저장할값

#define GET(p) (*(unsigned int *)(p)) // p가 참조하는 워드 반환 (포인터라서 직접 역참조 불가능 ->타입캐스팅 )
#define PUT(p,val) (*(unsigned int *)(p) = (unsigned int)(val)) // p에 val 저장

// 각 주소 p에 있는 헤더 또는 푸터의 사이즈와 할당 비트를 리턴한다.
#define GET_SIZE(p) (GET(p) & ~0x7) // 사이즈 (~0x7 : ...11111000, '&'연산으로 뒤에 세자리 없어짐) 16진수인 0x7을 2진수로 바꾸면 1111이라 ~연산자를 사용해서 뒷자리를 전부 0으로 바꾸는것임
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 상태

// 각각 헤더와 풋터를 가리키는 포인터를 리턴한다.
#define HDRP(bp) ((char *)(bp) - WSIZE) // header 포인터
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer 포인터(헤더의 정보를 참조해서 가져오기 때문에, 
//헤더의 정보를 변경했다면 변경된 위치의 footer 가 반환됨
//ㅡ다음 블록의 블록 포인터, 이전 블록의 블록 포인터

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char*)(bp)-WSIZE))) //다음블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))// 이전블록의 포인터

// for segregated list
static void *heap_listp; // 클래스의 시작
#define GET_SUCC(bp) (*(void **)((char*)(bp)+WSIZE)) //다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)((char*)(bp)))// 이전 가용 블록의 주소
#define GET_ROOT(class) (*(void **)((char *)(heap_listp)+(WSIZE * class)))

static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
int mm_init(void);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
void mm_free(void *ptr);

void *mm_realloc(void *ptr, size_t size);
static void splice_free_block(void *bp); // 가용 리스트에서 제거
static void add_free_block(void *bp);    // 가용 리스트에 추가
static int get_class(size_t size);

/*
Block:  F [ HDR | NEXTP | PREVP | FTR ] 
        A [ HDR |    PAYLOADS   | FTR ]
Bytes:      4      8        8      4   ==> MIN_BLK_SIZE = 24 bytes
*/

int mm_init(void) // ??? 왜 이사이즈인지 ...모르겠습니다...
{
    // 힙 초기화하기 (시스템 호출이 실패하면 -1을 반환함)
    // ??? 왜 이크기인지... 16바이트 * 4 
   if((heap_listp = mem_sbrk((SEGREGATE_SIZE+4)*WSIZE)) == (void*) -1){
    return -1;
   }

    PUT(heap_listp, 0);  // Alignment padding (힙의 시작주소에 0 할당)

    PUT(heap_listp + (1 * WSIZE) , PACK((SEGREGATE_SIZE + 2)* WSIZE, 1)); // 프롤로그 헤더 크기: 헤더1+ 푸터1+segregated list 크기
    
    for (int i=0; i<SEGREGATE_SIZE; i++){
        PUT(heap_listp + ((2+i)*WSIZE), NULL); // ???
    }
    PUT(heap_listp + ((SEGREGATE_SIZE +2)*WSIZE), PACK((SEGREGATE_SIZE+2)*WSIZE,1));// 프롤로그 Footer
    // 에필로그 블록의 주소를 명시적 가용 리스트의 head로 설정
    PUT(heap_listp + ((SEGREGATE_SIZE+3)*WSIZE), PACK(0,1));// 에필로그 header: 프로그램이 할당한 블록의 뒤에 위치
    heap_listp += (2*WSIZE);
    
    return 0;
}


static void *extend_heap(size_t words)
{
    char *bp;
    char *start_bp;
    // 더블 워드 정렬 유지
    // size: 확장할 크기
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해서 곱함)

    if ((long)(start_bp = mem_sbrk(size)) == -1) // 자리 없을 때 힙 확장
        return NULL;

    bp = start_bp;
    size_t page_size = size / PAGE_REQUEST_SIZE; //한 블록의 크기
    while (size >= page_size){
        size -= page_size;
        PUT(HDRP(bp), PACK(page_size,0));// 새 빈 블록 헤더 초기화
        add_free_block(bp);
        bp += page_size;
    }
    return start_bp;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */


void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 사이즈
    size_t extendsize; // 확장할 사이즈
    char *bp;

    if (size == 0) // 잘못된 요청 분기
        return NULL;

    if (size <= DSIZE)     // 8바이트 이하이면
        asize = 2 * DSIZE; // 최소 블록 크기 16바이트 할당 (헤더 4 + 푸터 4 + 저장공간 8)
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); // 8배수로 올림 처리

    if ((bp = find_fit(asize)) != NULL) // 가용 블록 검색
    {
        place(bp, asize); // 할당
        return bp;        // 새로 할당된 블록의 포인터 리턴
    }

    // 적합한 블록이 없을 경우 힙확장
    extendsize = asize * PAGE_REQUEST_SIZE; // PAGE_REQUEST_SIZE 배수만큼 추가 메모리를 요청
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


static void place(void *bp, size_t asize)
{
    splice_free_block(bp); // free_list에서 해당 블록 제거
    PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));// 해당블록 전부 사용
}

static void *find_fit(size_t asize)
{
    int class = get_class(asize);

    void *bp = GET_ROOT(class); // 클래스의 루트 주소
    while (class < SEGREGATE_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
    {
        bp = GET_ROOT(class);
        while(bp != NULL){
            if(asize <=GET_SIZE(HDRP(bp))){ // 적합한 사이즈의 블록을 찾으면 반환
                return bp; 
            }else{
                bp = GET_SUCC(bp);// 다음 가용 블록으로 이동.
            }
        }
        class+=1;
    }
    return NULL;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size  = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    add_free_block(ptr);
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
    if (size <= 0){ // size가 0인 경우 메모리 반환만 수행
        mm_free(ptr);
        return 0;
    }
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
      return NULL; // 할당 실패

    //   데이터 복사
    copySize = GET_SIZE(HDRP(ptr))- DSIZE; 

    if (size < copySize) // 기존 사이즈가, 새크기보다 더크면
      copySize = size; //size로 크기 변경
      // 기본 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사

    memcpy(newptr, oldptr, copySize); // 새 블록으로 데이터 복사
    // 기존 블록 반환
    mm_free(oldptr);
    return newptr;
}

//가용리스트에서 bp에 해당하는 블록을 제거하는 함수.
static void splice_free_block(void *bp)
{
     int class = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class)) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class)); // 다음 블록을 루트로 변경
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
    int class = get_class(GET_SIZE(HDRP(bp)));
    GET_SUCC(bp) = GET_ROOT(class);     // bp의 해당 가용 리스트의 루트가 가리키던 블록
    if (GET_ROOT(class) != NULL)        // list에 블록이 존재했을 경우만
        GET_PRED(GET_ROOT(class)) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    GET_ROOT(class) = bp;
}

// 적합한 가용 리스트를 찾는 함수
int get_class(size_t size)
{

    // 클래스별 최소 크기
    size_t class_sizes[SEGREGATE_SIZE];
    class_sizes[0] = 16;

    // 주어진 크기에 적합한 클래스 검색
    for (int i = 0; i < SEGREGATE_SIZE; i++)
    {
        if (i != 0)
            class_sizes[i] = class_sizes[i - 1] << 1;
        if (size <= class_sizes[i])
            return i;
    }

    // 주어진 크기가 8192바이트 이상인 경우, 마지막 클래스로 처리
    return SEGREGATE_SIZE - 1;
}

printf('커밋테스트');