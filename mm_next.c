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

/*과제 1) explicit /


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 /*64비트에서 돌릴 거라 4->8로 바꿈*/
#define DSIZE 8 /*64비트에서 돌릴 거라 8->16로 바꿈*/
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word (32bit) */
#define PACK(size, alloc) ((size) | (alloc)) /*크기와 할당비트를 통합하여 헤더와 풋터에 저장될 수 있는 값 리턴*/

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p)) 				/*인자p가 참조하는 워드를 리턴*/
#define PUT(p, val) (*(unsigned int *)(p) = (val))  /*인자p가 가리키는 워드에 val 저장*/

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)  /*크기 리턴. 헤더 정보에 있는 사이즈의 크기만 가져옴.*/
#define GET_ALLOC(p) (GET(p) & 0x1)  /*할당비트 리턴*/

/* 블록포인터 bp에 대하여, 헤더와 푸터 주소 계산. bp는 payload의 시작점의 포인터. */
#define HDRP(bp) ((char *)(bp) - WSIZE)							//블록의 헤더가 가리키는 포인터 리턴. bp - Wsize(4비트)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)    //블록의 푸터가 가리키는 포인터 리턴. bp + 내 사이즈??- Dsize

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //다음 블록의 bp 리턴. 현재 bp + HDRP의 크기
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //이전 블록의 bp 리턴. 현재 bp - 

/*함수 선언을 앞에 쓰면 함수 순서 관계없이 코드 작성 가능*/
static void *coalesce(void *bp); 
static void *extend_heap(size_t words);
int mm_init(void);
// static void *find_fit(size_t asize);
static void *find_next_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);


static char *heap_listp; /*p824*/
static char *last_bp;


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1;

	PUT(heap_listp, 0); //Alignment padding
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //Prologue header. heap_listp + Wsize가 가리키는 워드에 pack(Dsize, 1) 값 저장
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //Prologue footer.
	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); //Epilogue header
	last_bp = heap_listp + (2*WSIZE);
	heap_listp += (2*WSIZE); 

	/* Extends the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
	
	last_bp = (char*)heap_listp; //heap_listp는 void였기 때문에 last_bp에 맞게 char형으로 반환
	return 0;
}

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;
	
	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL; //bp는 이전 힙의 마지막 블록 +1 위치 리턴
	
	/*Initialize free block header / footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); // Free block header
	PUT(FTRP(bp), PACK(size, 0)); // Free block footer
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header 

	/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) // size byte
{
	size_t asize; // 블록 사이즈 조정
	size_t extendsize; // 힙 확장 사이즈
	char *bp; //블록포인터

	/* Ignore spurious requests (size == 0) */
	if (size == 0)
        return NULL;
	
	/* Adjust block size to include overhead and alignement reqs */
	if (size <= DSIZE)
        asize = 2*DSIZE; // if size is under 8bytes (double words)
	else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

	/* 사이즈에 맞는 free list 탐색 */
	if ((bp = find_next_fit(asize)) != NULL){
		place(bp, asize);
		last_bp = bp;
		return bp;
	}

	/* 사이즈에 맞는 free list가 없는 경우, 추가적으로 힙 영역 요청 및 배치 */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
	place(bp, asize);
	last_bp = bp;
	return bp;
}


void *find_next_fit(size_t asize) {
    char *bp = last_bp; // start from the most recently allocated block

	for (bp= heap_listp; GET_SIZE(HDRP(bp)) > 0; bp= NEXT_BLKP(bp)){
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
			last_bp = bp;
			return bp;
		}
	}

	bp = heap_listp;
	while (bp < last_bp){
		bp = NEXT_BLKP(bp);
		if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize){
			last_bp = bp;
			return bp;
		}
	}

    return NULL; // no free block found
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // csize = 현재 블록크기

    if ((csize - asize) >= (2*DSIZE)){
		//요청받은 용량만큼 블록배치
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
		bp = NEXT_BLKP(bp);

		//남는 블록에 header, footer 배치
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //Previous block allocation
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //Next block allocation 
	size_t size = GET_SIZE(HDRP(bp)); // Current block size
	
	/* Case 1 : both allocated -> just return bp */
	if (prev_alloc && next_alloc) {
		last_bp = bp;
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
	last_bp = bp;
	return bp;
}




/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//       return NULL;
//     copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     if (size < copySize)
//       copySize = size;
//     memcpy(newptr, oldptr, copySize);
//     mm_free(oldptr);
//     return newptr;
// }
void *mm_realloc(void *bp, size_t size) {
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE);   // 2*WISE는 헤더와 풋터

    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
    if (new_size <= old_size) {
        return bp;
    }
    // new_size가 old_size보다 크면 사이즈 변경
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
        if (!next_alloc && current_size >= new_size) {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        // 아니면 새로 block 만들어서 거기로 옮기기
        else {
            void *new_bp = mm_malloc(new_size);
            place(new_bp, new_size);
            memcpy(new_bp, bp, new_size);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
            mm_free(bp);
            return new_bp;
        }
    }
}











