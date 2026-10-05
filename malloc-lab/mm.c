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
 * 
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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8//8바이트 정렬 사용

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))//size_t값을 저장하는데 필요공간

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)//힙이 부족할때 확장크기
#define MAX(x,y) ((x)>(y)?(x):(y))//max(20,40)이면 40 (둘중큰값반환)

//헤더만들기
#define PACK(size,alloc) ((size)|(alloc))//블록크기와 할당여부 팩

//p가 가리키는 메모리에 저장된값 읽고 쓰기
#define GET(p) (*(unsigned int *)(p))//만약 size가 32이고 alloc이 1이면 32 
#define PUT(p,val) (*(unsigned int *)(p) = (val))//alloc 1

//사이즈 얼록 추출하기 (3바이트 비어있으면)

#define GET_SIZE(p) (GET(p)& ~0x7)
#define GET_ALLOC(p) (GET(p)& 0x1)

//블록포인트의 헤더와 푸터주소 구하기
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp))-DSIZE)

//다음과 이전 블록포인터 주소계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))//현재블록크기를 이용해서 다음블록 페이로드 계산
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))//이전블록 푸터 크기읽어서 이전페이로드 계산

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))
            + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp=PREV_BLKP(bp);

    }
    return bp;
}

// extend_heap
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    //워드가 홀수면 정렬하기위해서 짝수로 올림계산해서 바이트 변환
    size = (words %2)?(words+1) *WSIZE : words * WSIZE;//다음 공간 확보
    if ((long)(bp = mem_sbrk(size))==-1)
        return NULL;

    //반환된 블록 헤더 푸터 에필로그
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));//확장되면 새 에필로그 헤더 다시씌우기

    return coalesce(bp);//앞뒤 프리블록 있으면 합치기
}

/*
 * mm_init - initialize the malloc package.
 */
static char *heap_listp;
int mm_init(void)
{
    //새 힙 만들기
    if ((heap_listp = mem_sbrk(4*WSIZE))==(void*)-1)//16바이트 확보
        return -1;
    PUT(heap_listp,0);//패딩
    PUT(heap_listp +(1*WSIZE),PACK(DSIZE,1));//프롤로그 헤더
    PUT(heap_listp + (2*WSIZE),PACK(DSIZE,1));//프롤로그 푸터
    PUT(heap_listp + (3*WSIZE),PACK(0,1));//에필로그 헤더
    heap_listp += (2*WSIZE);//heap_listp 주소를 8바이트 이동시켜 프롤로그 푸터 위치를 가리키게함

    if(extend_heap(CHUNKSIZE/WSIZE)==NULL)//워드 개수
        return -1;//청크사이즈만큼 늘려 힙공간 확장
    return 0;
}
static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)); bp=NEXT_BLKP(bp)){//힙 순회
        if (GET_ALLOC(HDRP(bp)) == 0)//alloc이 0일때
            if(GET_SIZE(HDRP(bp))>=asize)
            return bp;
    }
    return NULL;
}

static void place(void *bp,size_t asize)//사용자가 만약 asize 24 
{
    size_t old_size;

    old_size = GET_SIZE(HDRP(bp));

    if(old_size - asize >= DSIZE){//기존 64-24=40 헤더만들어야됨
        void *next_bp = (char*)bp+asize;
        //앞쪽
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
        //뒤쪽 프리

        PUT(HDRP(next_bp),PACK(old_size - asize,0));
        PUT(FTRP(next_bp),PACK(old_size - asize,0));
    }else{//asize가 16일때 oldsize가 24이면 작아서 쪼개지않고 전체씀
        PUT(HDRP(bp),PACK(old_size,1));
        PUT(FTRP(bp),PACK(old_size,1));
    }
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

    if(size == 0)
        return NULL;//사용요청 크기가 0이면 null 반환

    if (size <= DSIZE)
        asize = 2*DSIZE;//16바이트 크기구성
    else
        asize = DSIZE * ((size + (DSIZE)+(DSIZE-1))/DSIZE);//?
    
    //기존 빈공간 검색
    if((bp = find_fit(asize))!=NULL){
        place(bp,asize);
        return bp;
    }
    //없으면 확장
    extendsize = MAX(asize,CHUNKSIZE);

    if ((bp=extend_heap (extendsize/WSIZE))==NULL)
        return NULL;

    //새로만든 프리블록 사용
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.프리구현

 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    coalesce(ptr);
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)//새 블록을 만들고 기존데이터를 복사한다음에 기존블록을 프리함
{
    void *oldptr = ptr;//기존 블록포인터를 oldptr에저장
    void *newptr;//새로운블록 포인터 (주소)
    size_t copySize;//사이즈 정보를 새 블록포인트로 복사?

    newptr = mm_malloc(size);//새로운크기의 블록을 할당함
    if (newptr == NULL) //새블록이 null일때 null반환
        return NULL;

    copySize = GET_SIZE(HDRP(oldptr));//oldptr 앞에 기존블록포인터 정보를 가져옴
    
    if (size < copySize)//새 정보가 기존 정보보다 작을때
        copySize = size;//기존 정보가 새정보가 됨
    
    memcpy(newptr, ptr, copySize);// 기존블록의 데이터를 새블록으로 copysize만큼 복사
    
    mm_free(oldptr);//기존블록 블록포인터 프리
    return newptr;//새로운 블록정보를 반환
}