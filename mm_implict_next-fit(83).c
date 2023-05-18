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
    " ",
    /* Second member's email address (leave blank if none) */
    "@gmail.com"
    /* Second member's full name (leave blank if none) */
    " ",
    /* Second member's email address (leave blank if none) */
    "@gmail.com"
};

/*과제 1) explicit /
/*https://dapsu-startup.tistory.com/entry/Malloc-Lab-%EB%8F%99%EC%A0%81-%EB%A9%94%EB%AA%A8%EB%A6%AC-%ED%95%A0%EB%8B%B93-Implicit-first-fit-next-fit-%EC%BD%94%EB%93%9C-%EA%B5%AC%ED%98%84
이 블로그 참고했음.*/


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
#define GET_SIZE(p) (GET(p) & ~0x7)  /*크기 리턴. 헤더 정보에 있는 사이즈의 크기만 가져옴.*/
#define GET_ALLOC(p) (GET(p) & 0x1)  /*할당비트 리턴. 할당이면 1 free면 0*/

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
static void *find_next_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);


static char *heap_listp; //p824
static void *last_bp;


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

	last_bp = heap_listp + (2*WSIZE);
	heap_listp += (2*WSIZE); 

	/* Extends the empty heap with a free block of CHUNKSIZE bytes 청크 사이즈만큼 힙을 확장해 초기 가용 블록 생성. */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // chunk size 확인(받을 수 있는 사이즈인지)
		return -1; 

	//초기 last_bp는 heap_listp가 가리키는 메모리블록의 주소를 가리킴
	last_bp = (char*)heap_listp; //heap_listp는 void라 주소연산이 불가능했기 때문에 last_bp에 맞게 char형으로 반환.
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
	PUT(HDRP(bp), PACK(size, 0)); // Free block header 초기에는 할당비트를 0(free)로 줌.
	PUT(FTRP(bp), PACK(size, 0)); // Free block footer
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header  다음 sbrk 호출 시 새로운 free block의 Header가 됨

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
	if (size == 0) // 만약 입력받은 사이즈가 0이면 무시
        return NULL;
	
	/* Adjust block size to include overhead and alignement reqs */
	if (size <= DSIZE) // 만약 입력받은 사이즈가 DSIZE보다 작을지라도 최소 블록SIZE(2*DSIZE)로 생성
        asize = 2*DSIZE; 
	//8바이트 넘는 요청 : 오버헤드(블록 내에서 payload를 제외한 모든 것=헤더,푸터) 바이트 내에 더해주고, 가까운 8의 배수로 반올림
	else //할당요청의 용량이 2words 초과하면, 충분한 8바이트의 배수의 용량 할당
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

	/* 사이즈에 맞는 free list 탐색 */
	if ((bp = find_next_fit(asize)) != NULL){
		place(bp, asize); //초과부분을 분할하고 새롭게 할당한 블록의 포인터 반환
		last_bp = bp;
		return bp;
	}

	/* 사이즈에 맞는 free list가 없는 경우, 추가적으로 힙 영역 요청 및 배치 */
	// 맞는 free block이 없을 때
    // 힙을 새로운 free block으로 확장하고,
    // extend_heap으로 힙을 새로운 free block으로 확장(메모리 공간 더 할당), 
    // 요청한 블록을 새로운 free block에 배치(place)
	extendsize = MAX(asize, CHUNKSIZE); // 만약 chunk size보다 클 경우, 둘 중 더 큰 값으로 사이즈를 정한다.
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  // 단위 변환을 위해서 워드 사이즈로 바꿔주기 위해서 나눈다. 넘긴 사이즈만큼의 heap을 할당 받는다.
        return NULL;
	place(bp, asize); // 사이즈 늘린 상태에다가 bp주소에 asize를 배치
	last_bp = bp;
	return bp;
}


/*next_fit 마지막에 할당된 블록을 기준으로 다음 블록 검색 */
void *find_next_fit(size_t asize) { 
    char *bp = last_bp; // 마지막에 할당된 블록에서 시작

	for (bp= NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp= NEXT_BLKP(bp)){ //마지막 블록의 다음블록에서 시작해서 bp를 계속 다음블록포인터로 바꿔가며 사이즈가 0이 아닌 블럭을 찾아 for문 탐색
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ //현재블록이 가용블록이고 현재 블록 사이즈가 할당사이즈보다 이상이면
			last_bp = bp;
			return bp;
		}
	}

	bp = heap_listp;
	while (bp < last_bp){ // bp가 last_bp보다 앞에 있을 동안(=마지막 블록에 도달하기 직전까지. 마지막 블록에서는 bp = last_bp.)
		bp = NEXT_BLKP(bp); // 다음블록의 bp를 bp로 계속 갱신함.
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))){ //현재블록이 가용블록이고 현재 블록 사이즈가 할당사이즈보다 이상이면
			last_bp = bp;
			return bp;
		}
	}

    return NULL; // no free block found 조건에 맞는 아무 블록도 찾지 못할 시 NULL반환
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
 * place(bp, size) : size만큼 할당 후 남는 부분이 분할되었다면 free 블록 처리를 해준다.
 */
static void place(void *bp, size_t asize) // free블록에 배치시키는 함수
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)){ // 삽입하고 자리가 남으면(나머지가 최소블록크기보다 크면) split 해준다.
		//헤더와 풋터에 요청받은 용량만큼 현재 블록에 배치(1은 할당된 블록)
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
		bp = NEXT_BLKP(bp);

		//이제 bp는 다음 블록포인터임. 다음블럭에 나머지 사이즈와 free를 헤더와 풋터에 할당함.
        PUT(HDRP(bp), PACK(csize-asize, 0)); 
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else { // 나머지가 2*DSIZE(최소 가용 블록 크기)보다 적게 남으면 모두 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size); //다른 곳에 다시 할당받기

    if (newptr == NULL) // 실패하면 NULL 리턴
      return NULL;
    
	copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE); // 원래 블록사이즈

    if (size < copySize) //요청한 사이즈가 원래 블록사이즈보다 작다면 작은사이즈로 카피함.
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr); //기존 사이즈는 삭제
    return newptr;
}




