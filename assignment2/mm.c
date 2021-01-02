/*
 * mm-implicit.c -  Simple allocator based on implicit free lists,
 *                  first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      31                     3  2  1  0
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      -----------------------------------
 *
 * where s are the meaningful size bits and a/f is set
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap
 *  -----------------------------------------------------------------
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/*
 * If NEXT_FIT defined use next fit search, else use first fit search
 */
#define NEXT_FITx



/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* Global variables */
static char *_heap_listp;  /* pointer to first block */
#ifdef NEXT_FIT
static char *rover;       /* next fit rover */
#endif

static int _heap_ext_counter=0;

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);

char* get_heap_listp() {
    return _heap_listp;
}
char* set_and_get_heap_listp(char* ptr) {
    _heap_listp = ptr;
    return _heap_listp;
}

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void)
{
    /* create the initial empty heap */
    if (set_and_get_heap_listp(mem_sbrk(4*WSIZE)) == (void *)-1)
	return -1;
    PUT(get_heap_listp(), 0);                        /* alignment padding */
    PUT(get_heap_listp()+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */
    PUT(get_heap_listp()+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */
    PUT(get_heap_listp()+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    set_and_get_heap_listp(get_heap_listp()+DSIZE);

#ifdef NEXT_FIT
    rover = get_heap_listp();
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return -1;
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
    size_t asize, aword;
    char* bp;

    // 입력받은 사이즈에 header와 footer의 사이즈(OVERHEAD)를 더한 것을 Word size로 나누어 필요한 Word의 개수를 구한다.
    // 이때, 나눈 값은 올림한다.
    aword = (size+OVERHEAD+WSIZE-1)/WSIZE;

    // double align 된 사이즈로 맞춰 결과적으로 할당해야할 byte수를 구한다.
    asize = (aword % 2) ? (aword+1) * WSIZE : aword * WSIZE;

    // asize만큼이 들어갈 수 있는 free block을 찾는다.
    bp = find_fit(asize);

    // 알맞은 공간이 없는 경우
    if (bp == NULL){
        // heap을 늘려 새로운 free block을 만든다.
        bp = extend_heap(aword);
    	if (bp == NULL) return NULL;
    }

    // 위에서 찾은 free block에 asize만큼을 allocate 한다.
    place(bp, asize);
    return bp;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size;

    if (bp == NULL) return;
    size = GET_SIZE(HDRP(bp));

    // block이 이미 free 상태일 경우
    if (!GET_ALLOC(HDRP(bp))) {
        printf("Error: %p is already free\n", bp);
        return;
    }

    // free할 block의 header와 footer의 a/f 상태를 0(free)로 만들어준다.
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // free된 블록의 앞/뒤에 free 블록이 있을 경우
    // free 블록들을 coalesce한다.
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    int count;
    char* tmp_ptr, *next_brk;
    size_t old_size, asize, aword;

    // 넘겨받은 ptr이 NULL 인 경우
    // mm_malloc을 호출한다.
    if (ptr == NULL) return mm_malloc(size);

    // 넘겨받은 size가 0 인 경우
    // mm_free를 호출한다.
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // mm_malloc과 동일
    aword = (size+OVERHEAD+WSIZE-1)/WSIZE;
    asize = (aword % 2) ? (aword+1) * WSIZE : aword * WSIZE;

    // 블록의 원래 사이즈를 구한다.
    old_size = GET_SIZE(HDRP(ptr));

    // realloc할 size가 원래 size와 같은 경우
    // 아무것도 하지 않는다.
    if (asize == old_size) return ptr;

    // realloc할 size가 원래 size보다 작은 경우
    if (asize < old_size){
        // asize만큼 공간의 첫부분부터 할당하고,
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        tmp_ptr = NEXT_BLKP(ptr);
        // 남은 뒷부분에 남은 사이즈만큼을 free block으로 만든다.
        PUT(HDRP(tmp_ptr), PACK(old_size-asize, 0));
        PUT(FTRP(tmp_ptr), PACK(old_size-asize, 0));

        // 뜃부분에 free block이 있는 경우
        // 두 free block을 coalesce한다.
        coalesce(tmp_ptr);

        return ptr;
    }

    // realloc할 size가 원래 size보다 큰 경우
    // mm_malloc을 통해 새로운 공간을 할당받는다.
    tmp_ptr = mm_malloc(asize);
    // 원래 값을 새롭게 할당받은 주소로 복사한다.
    memcpy(tmp_ptr, ptr, old_size-OVERHEAD);
    // 원래 공간은 free block으로 만든다.
    mm_free(ptr);
    return tmp_ptr;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose)
{
    char *bp = get_heap_listp();

    if (verbose)
	printf("Heap (%p):\n", get_heap_listp());

    if ((GET_SIZE(HDRP(get_heap_listp())) != DSIZE) || !GET_ALLOC(HDRP(get_heap_listp())))
	printf("Bad prologue header\n");
    checkblock(get_heap_listp());

    for (bp = get_heap_listp(); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose)
	    printblock(bp);
	checkblock(bp);
    }

    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    _heap_ext_counter++;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1)
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (DSIZE + OVERHEAD)) {
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
#ifdef NEXT_FIT
    /* next fit search */
    char *oldrover = rover;

    /* search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;

    /* search from start of list to old rover */
    for (rover = get_heap_listp(); rover < oldrover; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;

    return NULL;  /* no fit found */
#else
    /* first fit search */
    void *bp;

    for (bp = get_heap_listp(); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
	    return bp;
	}
    }
    return NULL; /* no fit */
#endif
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    }

#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp)))
	rover = bp;
#endif

    return bp;
}


static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
	   hsize, (halloc ? 'a' : 'f'),
	   fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}


