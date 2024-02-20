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
    "Number 1 Team",
    /* First member's full name */
    "LEE Jae Won",
    /* First member's email address */
    "tpqms775@google.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 가용리스트 조작 매크로
#define WSIZE 4 // 워드크기
#define DSIZE 8 // 더블 워드크기
#define CHUNKSIZE (1 << 12)             // 현대의 운영체제의 페이지 크기인 4KB 페이지와 메모리 크기가 일치하여 효율적으로 사용 가능
//4096 2의 12승 비트연산을 사용

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))        // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴

#define GET(p)(*(unsigned int *)(p))                // 인자 p가 참조하는 워드를 읽어서 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // 인자 p가 가르키는 워드에 val을 저장

#define GET_SIZE(p) (GET(p) & ~0x7)                 // 주소 p에 있는 헤더 또는 풋터의 size와 리턴한다. p의 메모리 블록의 크기를 추출하기위해 사용
#define GET_ALLOC(p) (GET(p) & 0x1)                 // 주소 p에 있는 헤더 또는 풋터의 할당비트를 리턴한다. p의 메모리블록 할당여부를 확인하기위해 사용

#define HDRP(bp) ((char *)(bp)-WSIZE)                           //블록 헤더를 가리키는 포인터를 리턴 -> 데이터의 시작주소에서 헤더의 크기인 4바이트를 빼서 헤더의 시작주소를 나타냄
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)    //블록 풋터를 가리키는 포인터를 리턴 -> 데이터의 시작주소에서 헤더에 저장된 크기를 더해서 8바이트를 뺴서 푸터의 시작주소를 나타냄
                                                                // 헤더의 시작주소가 아닌 데이터의 시작주소 부터 시작해서 8바이트를 뺸다.

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))       // 다음 블록의 페이로드 시작 포인터를 리턴
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))       // 이전 블록의 페이로드 시작 포인터를 리턴

// 가용리스트 조작 매크로

static void *heap_listp;
int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
static void *coalesce(void *bp);
void *mm_realloc(void *ptr, size_t size);
static void *find_fit(size_t asize);
static void *next_fit(size_t asize);
static void place(void *bp, size_t aszie);
static void *find_nextp;

/*
 * mm_init - initialize the malloc package.
 */



int mm_init(void)
{
    //mem_sbrk 는 리눅스 시스템에서 sbrk로 대체할 수 있다. mem_sbrk는 다양한 운영체제에서 사용한다.
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)   //초기 메모리 블록을 요청하고 그결과를 heap_listp에 할당한다.
        return -1;                                          // 할당에 실패하면 (void *)-1를 반환하는데 반환값과 (void *)-1를 비교해서 할당실패이면 -1을 반환한다.
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  //헤더로 구성된 8바이트 블록
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  //푸터로 구성된 8바이트 블록
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      //에필로그 블록 크기가 0
    heap_listp += (2 * WSIZE);                      //프롤로그 블록과 에필로그 블록 사이 힙의 시작 주소를 나타냄
    find_nextp = heap_listp; // next_fit을 사용할 떄 필요한 변수

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words)                          // 힙영역을 확장하는 역할 입력받은 words의 크기를 기반으로 확장할 힙의 크기 계산
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;   // 확장할 힙의 바이트 크기단위 -> words가 홀수 인경우 한워드를 더 추가하여 더블 워드 정렬을 유지한다.
    if ((long)(bp = mem_sbrk(size)) == -1)                      // mem_sbrk함수를 호출하여 힙을 size 바이트 만큼 확장한다. -> 힙의 끝을 size 만큼 이동시키고 확장된 영역의 시작주소를 반환한다.
        return NULL;                                            // 확장을 실패하여 -1을 반환하면 NULL을 반환하여 오류를 나타낸다.

    PUT(HDRP(bp), PACK(size, 0));                               // bp는 에필로그 블록의 끝을 가르키고 있고 헤더의 포인터를 구하면 에필로그블록의 헤더의 시작위치로 바뀌고 헤더의 값은 사이즈와 비할당으로 바뀐다
    PUT(FTRP(bp), PACK(size, 0));                               // 푸터는 헤더에 기록된 사이즈만큼 정보가 변경된다.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                       // 새로운 에필로그 헤더를 설정한다. 

    return coalesce(bp);                                        //뒤에는 에필로그 블록이 할당된 상태이므로 앞의 블록이 할당된 경우의 여부에 따라 병합을 진행한다.
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0)                                                   // 요청된 크기가 0인경우 할당할 필요가 없음으로 NULL반환
        return NULL;

    // if(size <= DSIZE)                                            // 할당하려는 사이즈가 DSIZE(8바이트)보다 작은경우  최소 2*DSIZE 크기를 할당한다. 
    //     asize = 2*DSIZE;                                         // 헤더와 푸터와 정렬 요구사항을 충족하기위해 DSIZE는 헤더와 푸터밖에 못넣음
 
    // else                                                         
    //     asize = DSIZE * ((size + (DSIZE)+(DSIZE -1)) / DSIZE);   // 요청된 크기가 DSIZE(8바이트)보다 큰 경우, 크기를 DSIZE의 배수로 반올림한다.

    asize= ALIGN(size) + ALIGNMENT;                                 // 사이즈 크기를 최소 8의 배수로 반환한 후 포인터의 크기인 8바이트를 더한후 크기를 구한다.

    if((bp = find_fit(asize)) != NULL){                             // 구한 크기의 블록이 들어갈 수 있는 곳(크기가 크고 할당되지 않은 블록)을 찾은 후 메모리 할당을 수행
        place(bp, asize);                                           // 메모리 할당을 수행한다. 메모리가 남는경우 블록을 분할하고 할당된 블록의 메타데이터를 업데이트 한다.
        return bp;                                                  // 할당한 페이로드의 시작 주소를 반환한다.
    }

    extendsize = MAX(asize, CHUNKSIZE);                             // 확장할 크기 -> 요청된 크기와 미리 정의된 청크의 크기중 더 큰 값을 결정
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)                // 적합한 블록을 찾지 못한경우 extend_heap 함수를 호출하여 메모리 풀을 확장한다.
        return NULL;                                                // 힙 확장 에러시 NULL 반환 -> 시스템이 더이상 메모리를 제공할 수 없어 NULL을 반환한다.
    place(bp,asize);                                                // 힙 확장후 블록 재할당
    return bp;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));  //free할 대상이 이용중이었던 크기를 구한다.

    PUT(HDRP(ptr), PACK(size, 0));      //헤더블록을 초기화 이용중이었던 크기와 사용중이지 않은 0 을할당
    PUT(FTRP(ptr), PACK(size, 0));      //푸터블록을 초기화 이용중이었던 크기와 사용중이지 않은 0 을할당
    coalesce(ptr);
}

static void *coalesce(void *bp)
{
    //다음이 가용인경우 합치기는 쉬운데 
    //이전이 가용인경우 가용인지 아닌지 판단하기가 어렵다. 결국 처음부터 다 탐색하는 방법 밖에 없는데
    //그래서 Boundary Tags를 활용하여 블록의 맨끝에 footer를 붙여 헤더와 내용과 동일하게 블록크기 + 할당정보를 넣는다.


    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전블록의 푸터에서 이용중인지 체크
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음블록의 헤더에서 이용중인지 체크
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 주소의 헤더에 저장된 크기 

    if (prev_alloc && next_alloc)       // #case.1 현재 블록 기준으로 앞뒤가 할당되어있는 경우 
    {
        return bp;                      //현재 주소 리턴
    }

    else if (prev_alloc && !next_alloc) // #case.2 앞의 블록은 할당되어있고 뒤의 불록은 할당되어있지 않은 경우
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  //다음 블록의 주소의 헤더의 크기와 현재 주소의 헤더에 저장된 크기를 더해서 가용블록의 크기를 정한다.
        PUT(HDRP(bp), PACK(size, 0));           //현재 블록의 헤더에 저장된 크기를 변경하고 0으로 바꾸어 할당되지 않은 상태를 나타낸다.
        PUT(FTRP(bp), PACK(size, 0));           //현재 헤더에 업데이트된 저장된 크기만큼 이동 후 푸터의 값을 바꾼다.
        //실제로 합쳐져서 초기화 되는게 아니고 헤더와 푸터의 값만 업데이트하여 내부에 값은 이전의 헤더와 푸터의 값이 남아있을 수 있다.
    }

    else if (!prev_alloc && next_alloc) // #case.3 앞의 블록은 할당되어있지 않고 뒤의 불록은 할당되어있는 경우
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      //이전블록의 헤더에 저장된 값을 현재 주소의 헤더에 저장된 크기와 더한다.
        //size += GET_SIZE(FTRP(PREV_BLKP(bp)));    //이전블록의 헤더와 푸터에 저장된 값은 동일하기 때문에 이렇게 변경해도된다. 근데 일반적으로 이전 포인터의 헤더 값을 가져온다
        PUT(FTRP(bp), PACK(size, 0));               //현재 블록의 푸터에 이전블록의 크기와 합쳐진 값을 업데이트 한다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    //앞의 블록과 합쳐지는 경우니까 이전블록의 헤더 포인터를 구해서 현재 크기 만큼 업데이트한다.
        bp = PREV_BLKP(bp);
    }
    else                                // #case.4 앞,뒤 둘다 할당되어있지 않은 경우
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  // 블록의 크기는 현재 블록의 크기 + 이전블록의 헤더에 저장된 크기 + 다음블록의 푸터에 저장된 크기
                                                                                //  size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))); 
                                                                                // 헤더와 푸터에 저장된 값은 같으므로 이렇게 변경해도 된다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                                // 이전블록의 헤더에 크기와 할당비트를 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                                // 다음블록의 푸터에 크기와 할당비트를 업데이트한다.
        bp = PREV_BLKP(bp);                                                     // 데이터의 시작주소는 이전 블록의 데이터 시작주소가 된다.
    }
    find_nextp = bp; // next_fit을 사용하기 위한 변수
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;    //확장대상의 포인터가 가르키는 블록크기

    // size가 0이면 free와 같은 동작
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // 할당된 블록이 없다면 malloc과 같은 동작
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);   // 새로운 메모리 블록 할당해서 할당에 실패하면 NULL을 반환한다
    if (newptr == NULL)         // 할당 실패시 이전 주소를 읽어버리지 않게 다른곳에 저장해논다.
        return NULL;

    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    //(char *)oldptr - SIZE_T_SIZE ->
    // 이전 블록의 데이터의 시작 지점에서 SIZE_T_SIZE만큼 이전으로 이동
    //SIZE_T_SIZE -> 헤더에 저장된 데이터의 크기를 나타냄

    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    //copySize = GET_SIZE(HDRP(oldptr)); 의 차이점

    //copySize = GET_SIZE(HDRP(oldptr));는 oldptr이 가리키는 메모리 블록의 헤더에서 크기를 읽어온다
    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);는 

    copySize = GET_SIZE(HDRP(oldptr))  - DSIZE; //payload크기만큼 복사
    if (size < copySize)
        copySize = size;

    //이전 포인터 블록의 크기를 헤더에 있는 정보에서 가져와서 copySize가 더 크면 크기를 줄이는 것이므로 size를 대입
    memcpy(newptr, oldptr, copySize);   // 새로운 포인터에 이전 포인터가 가르키는 내용 복사
    mm_free(oldptr);                    // 쓸모없어진 이전 포인터 free()
    return newptr;                      // 새로 할당된 포인터 반환
}


static void *find_fit(size_t asize){
    void *bp;               //탐색을 시작할 포인터
    bp = find_nextp;        //다음에 탐색을 시작할 위치를 가리키는 변수
    
    for(;GET_SIZE(HDRP(find_nextp)) > 0; find_nextp = NEXT_BLKP(find_nextp)){           // 할당가능한 블록이 존재할때 까지 루프를 반복한다. // 크기가 0인 에필로그 블록을 만날때까지
        if(!GET_ALLOC(HDRP(find_nextp))&& (asize <= GET_SIZE(HDRP(find_nextp)))){       // 현재 블록이 할당되지 않았고, 할당되지 않은 블록의 크기가 요청된 크기(asize)보다 크거나 같으면, 
            return find_nextp;                                                          // 현재 위치(find_nextp)를 반환합니다.
        }
    }
    for(find_nextp = heap_listp; find_nextp != bp; find_nextp =NEXT_BLKP(find_nextp)){  // 첫번째 루프에서 적절한 위치를 찾지 못한 경우 힙의 시작부터 다시 탐색을 시작한다.
                                                                                        // 처음 find_nextp가 가르키던 위치 bp까지 다시 검색한다.
        if (!GET_ALLOC(HDRP(find_nextp)) && (asize <= GET_SIZE(HDRP(find_nextp))))      // 현재 블록이 할당되지 않았고, 할당되지 않은 블록의 크기가 요청된 크기(asize)보다 크거나 같으면, 
        {                                                                               // 현재 위치(find_nextp)를 반환합니다.
            return find_nextp;
        }
        
    }
    
    return NULL;
}

static void place(void *bp, size_t asize){  //asize -> 요청된 크기
    size_t csize = GET_SIZE(HDRP(bp));      // 해당 포인터의 블록의 크기

                                                // 블록을 요청된 크기(asize)로 할당한 뒤 남는 공간이 2개의 더블워드 크기(2*DSIZE) 이상이라면, 
                                                // 블록을 두 부분으로 나눈다. 이는 할당 후 남는 공간이 충분히 커서 다른 요청을 수용할 수 있음
    if((csize - asize) >= (2*DSIZE)){           // 1개 워드 크기 이상이여도 공간을 나눌 수 있는데 너무 작은 블록을 생성하는 것은 단편화를 증가시키고 헤드 푸터의 값보다 작기때문에 효율적이지 않음
        PUT(HDRP(bp), PACK(asize, 1));          // 헤더의 데이터 부분에 할당한 크기와 할당중임을 표시
        PUT(FTRP(bp), PACK(asize, 1));          // 푸터의 데이터 부분에 할당한 크기와 할당중임을 표시
        bp = NEXT_BLKP(bp);                     // 다음 블록의 페이로드 시작 위치를 반환
        PUT(HDRP(bp), PACK(csize - asize, 0));  // 다음블록의 헤더에 할당하고 남은 부분을 헤더에 표시 후 0으로 바꾸어 할당되지 않음을 표시
        PUT(FTRP(bp), PACK(csize - asize, 0));  //           푸터          "
    }else{                                      // 할당한 뒤 남는 공간이 작아 분할이 불필요한 경우
        PUT(HDRP(bp), PACK(csize, 1));          // 분할하지 않고 현재 블록의 크기를 그대로 사용한다. 
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
