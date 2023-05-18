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
    "7team",
    /* First member's full name */
    "이연주",
    /* First member's email address */
    "mulverry@gmail.com",
    /* Second member's full name (leave blank if none) */
    "김상윤",
    /* Second member's email address (leave blank if none) */
    "@gmail.com"
    /* Second member's full name (leave blank if none) */
    "박정원",
    /* Second member's email address (leave blank if none) */
    "@gmail.com"
};

/*과제 1) explicit  2) next-fit구현*/


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 
#define DSIZE 8 
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word (32bit) */
#define PACK(size, alloc) ((size) | (alloc)) /*크기와 할당비트를 통합하여 헤더와 풋터에 저장될 수 있는 값 리턴*/

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p)) 				/*인자p가 참조하는 워드를 리턴*/
#define PUT(p, val) (*(unsigned int *)(p) = (val))  /*인자p가 가리키는 워드에 val 저장*/

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)   /*크기 리턴. 헤더 정보에 있는 사이즈의 크기만 가져옴. (0~7은 111로 3비트. 3비트를 제외한 나머지는 크기를 나타낸다.)*/
#define GET_ALLOC(p) (GET(p) & 0x1)  /*할당비트 리턴*/

/* 블록포인터 bp에 대하여, 헤더와 푸터 주소 계산. bp는 payload의 시작점의 포인터. */
#define HDRP(bp) ((char *)(bp) - WSIZE)							//블록의 헤더가 가리키는 포인터 리턴. bp - Wsize(4비트)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)    //블록의 푸터가 가리키는 포인터 리턴. bp + 헤더에 나와있는 내 사이즈- Dsize

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //다음 블록의 bp 리턴. 현재 bp + 현재블록 크기(헤더에 나온 내 사이즈)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //이전 블록의 bp 리턴. 현재 bp - 이전블록 크기(이전 블록 푸터에 나온 블록사이즈)

/*함수 선언을 앞에 쓰면 함수 순서 관계없이 코드 작성 가능*/
static void *coalesce(void *bp); 
static void *extend_heap(size_t words);
int mm_init(void);
static void *find_fit(size_t asize);
// static void *find_next_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);


static char *heap_listp; /*p824*/

/* 
 * mm_init - initialize the malloc package.
 // 초기 힙 생성
    // 4 words 사이즈의 빈 가용 리스트 초기화
    // 4 words 구성 : unused padding, prologue_header, prologue_footer, epilogue_header
 */
int mm_init(void)
{
	/* Create the initial empty heap */
	 // 처음에 mem_sbrk(4*WSIZE) 를 호출함으로써 heap_listp 의 시작 주소를 변경시켜 준다.
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //heap_listp가 힙의 최댓값이상을 요청하면 fail
		return -1;

	PUT(heap_listp, 0); //Alignment padding
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //Prologue header. heap_listp + Wsize가 가리키는 워드에 pack(Dsize, 1-할당됨) 값 저장
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //Prologue footer. heap_listp + 2*Wsize가 가리키는 워드에 pack(Dsize, 1-할당됨) 값 저장
	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); //Epilogue header
	heap_listp += (2*WSIZE); 

	/* Extends the empty heap with a free block of CHUNKSIZE bytes 청크 사이즈만큼 힙을 확장해 초기 가용 블록 생성.*/ */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // chunk size 확인(받을 수 있는 사이즈인지)
		return -1; 

	return 0;
}

static void *extend_heap(size_t words) // 워드 단위 메모리를 인자로 받아, 새 가용 블록으로 힙을 확장.
{
	char *bp;
	size_t size;
	
	/* Allocate an even number of words to maintain alignment 더블 워드 정렬에 따라 mem_sbrk함수로 추가 힙 메모리를 할당받는다.*/
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; //words가 홀수면 +1을 해서 공간할당, 짝수면 그냥 할당
	if ((long)(bp = mem_sbrk(size)) == -1) // // brk 포인터에 size만큼 더해서 힙을 늘림. 너무 커서 할당 못받으면 return -1
		return NULL; 
	
	/*Initialize free block header / footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); // Free block header. 초기에는 할당비트를 0(free)로 줌.
	PUT(FTRP(bp), PACK(size, 0)); // Free block footer.
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header. 다음 sbrk 호출 시 새로운 free block의 Header가 됨

	/* Coalesce if the previous block was free 이전 block이 free였다면 coalesce(연결) */
	return coalesce(bp);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	
	PUT(HDRP(bp), PACK(size, 0)); //헤더에 free라고 입력
	PUT(FTRP(bp), PACK(size, 0)); //풋터에 free라고 입력
	coalesce(bp); //연결
}

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //Previous block allocation
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //Next block allocation 
	size_t size = GET_SIZE(HDRP(bp)); // Current block size
	
	/* Case 1 : both allocated -> just return bp */
	if (prev_alloc && next_alloc) {
		return bp; 
	}
	/* Case 2 : next block free */
	else if (prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // Increase block size
		PUT(HDRP(bp), PACK(size, 0)); // Put size in header 
		PUT(FTRP(bp), PACK(size, 0)); // Put size in footer
	}
	/* Case 3 : prev block free -> move bp to start of prev block */
	else if (!prev_alloc && next_alloc) {
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	/* Case 4: both free */
	else {
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	return bp;
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) // size byte
{
	size_t asize; // 할당도니 블록사이즈
	size_t extendsize; // 힙 확장 사이즈
	char *bp; //블록포인터

	/* Ignore spurious requests (size == 0) */
	if (size == 0)
        return NULL;
	
	/* Adjust block size to include overhead and alignement reqs */
	if (size <= DSIZE)
        asize = 2*DSIZE; // if size is under 8bytes , 2Dsize로 할당요청
	else //할당요청의 용량이 2words 초과하면, 충분한 8바이트의 배수의 용량 할당
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

	/* 사이즈에 맞는 free list 탐색 */
	if ((bp = find_fit(asize)) != NULL) { //first-fit으로 찾기
		place(bp, asize);
		return bp;
	}

	/* 사이즈에 맞는 free list가 없는 경우, 추가적으로 힙 영역 요청 및 배치 */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
	place(bp, asize);
	return bp;
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


static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
    /*endif 안 넣었음*/
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
