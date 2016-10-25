/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */


#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif
/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Next and previous free nodes */
/*
#define NEXT_FREE(bp) ((char*)(*((size_t*)((char*)(bp)))))
#define PREV_FREE(bp) ((char*)(*((size_t*)((char*)(bp) + DSIZE))))

#define SET_NEXT(bp, val) (*((size_t*)((char*)(bp)))) = (size_t)(val)
#define SET_PREV(bp, val) (*((size_t*)((char*)(bp))+DSIZE)) = (size_t)(val)
*/
#define NEXT_FREE(bp) ((char*)(bp))
#define PREV_FREE(bp) (((char*)(bp)) + DSIZE)

#define GETP(bp) (*(char**)(bp))
#define PUTP(bp, val) (*(char**)(bp) = (val))

//#define P2I(bp)       ((unsigned long)(bp))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *free_head = NULL;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
//static void *coalesce(void *bp);

void mm_checkheap(int lineno);
//static int tortoise_and_hare(char* freehead);

//static void checkblock(void *bp);
/*
static void print_freelist() {
  char* bp = free_head;
  printf("\n[Linked list:]\n");

  if (bp == NULL) printf("[List empty]\n");

  for (bp = free_head; bp != NULL; bp = GETP(NEXT_FREE(bp))) {
    printf("%p : ", bp);
    printf("[%d | %d]--", GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
    printf("[%p | %p]--", GETP(NEXT_FREE(bp)), GETP(PREV_FREE(bp)));
    printf("[%d | %d] ", GET_SIZE(FTRP(bp)), GET_ALLOC(FTRP(bp)));
    if (bp == free_head) printf(" <free_head>\n");
  }
  printf("\n\n");

}
*/
/*
static void printblocks() {
  char *bp = heap_listp;
  if (bp == NULL) printf("[Heap empty]");
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    printf("%p : ", bp);
    printf("[%d | %d]--", GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
    printf("[%p | %p]--", NEXT_FREE(bp), PREV_FREE(bp));
    printf("[%d | %d]\n", GET_SIZE(FTRP(bp)), GET_ALLOC(FTRP(bp)));
  }
  printf("\n\n");
}
*/
static inline void free_add(void *bp) {
  /*
  printf("\n\n Adding this to the free list:\n");
  printf("%p : ", bp);
  printf("[%d | %d]--", GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
  printf("[%p | %p]--", GETP(NEXT_FREE(bp)), GETP(PREV_FREE(bp)));
  printf("[%d | %d]\n", GET_SIZE(FTRP(bp)), GET_ALLOC(FTRP(bp)));

  printf("\nBefore addition: \n");
  print_freelist();
  */
  //*((char**)NEXT_FREE(bp)) = NULL;

  PUTP(NEXT_FREE(bp), free_head);
  PUTP(PREV_FREE(bp), NULL);

  if (free_head != NULL) {
    PUTP(PREV_FREE(free_head), bp);
  }

  free_head = bp;
  /*
  if (tortoise_and_hare(free_head)) {
    printf("Circular.\n");
    exit(0);
  */
}
  /*
  printf("After addition:\n");
  print_freelist();
  */
//}

static inline void free_remove(void *bp) {

  //printf("Removing %p from the list\n", bp);

  if (GETP(NEXT_FREE(bp)) != NULL) {

    PUTP(PREV_FREE(GETP(NEXT_FREE(bp))), GETP(PREV_FREE(bp)));

  }
  if (GETP(PREV_FREE(bp)) != NULL) {
    PUTP(NEXT_FREE(GETP(PREV_FREE(bp))), GETP(NEXT_FREE(bp)));
  }

  if (bp == free_head) {
    //printf("Free-head\n\n\n");
    free_head = GETP(NEXT_FREE(free_head));
  }

  //SET_PREV(bp, NULL);
  //SET_NEXT(bp, NULL);

  //printf("After removal: \n");
  //  print_freelist();
  //printf("And heap: \n");
  //printblocks();
}

/*
 * mm_init - Initialize the memory manager
 */

int mm_init(void)
{
  free_head = NULL;
  heap_listp = 0;
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    return -1;
  PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);


    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}


/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */

void *mm_malloc(size_t size)
{

    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_listp == 0){
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 3*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    place(bp, asize);

    return bp;
}

static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) {            /* Case 1 */
    return bp;
  }

  else if (prev_alloc && !next_alloc) {      /* Case 2 */
    //    printf("Case 2\n");
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    free_remove(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size,0));

  }

  else if (!prev_alloc && next_alloc) {      /* Case 3 */
    //    printf("Case 3\n");
    //printf("This was just added: %p\n", bp);
    free_remove(bp);
    //printf("Then removed: %p\n", bp);
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    //printf("Now adding: %p\n", bp);
    //printf("Case 3\n");
    //free_add(bp);
  }

  else {
    //printf("Case 4\n");/* Case 4 */
    free_remove(bp);
    free_remove(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
      GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    //printf("Case 4\n");
    //free_add(bp);
  }

  return bp;
}

/*
 * mm_free - Free a block
 */

void mm_free(void *bp)
{
  //printf("Due to freeing.\n");
    if(bp == 0)
        return;
    size_t size = GET_SIZE(HDRP(bp));

    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    //    printf("In a free()\n");
    free_add(bp);

    coalesce(bp);

}


/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    mm_checkheap(215);
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * checkheap - We don't check anything right now.
 */


/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{

  //  printf("Due to heap extension: \n");
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    //    printf("call to free after expanding\n");
    free_add(bp);

    return coalesce(bp);
}


/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */

static void place(void *bp, size_t asize)

{
  //printf("\n\n\n Place \n\n\n");
  asize = asize;
  mm_checkheap(291);
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= (3*DSIZE)) {
    //printf("Place if\n");
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    free_remove(bp);
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
    free_add(bp);
  }
  else {
    //    printf("Place else\n");
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    free_remove(bp);

  }
  //    mm_checkheap(305);

}


/*
 * find_fit - Find a fit for a block with asize bytes
 */

/*
static int tortoise_and_hare(char* free_head){

  if (free_head == NULL)
    return 0;

  if (GETP(NEXT_FREE(free_head)) == NULL) {
    return 0;
  }

  char* tortoise = free_head;
  char* hare = GETP(NEXT_FREE(free_head));

  while (hare != tortoise) {

    if (hare == NULL) return 0;

    if (GETP(NEXT_FREE(hare)) == NULL ||
        GETP(NEXT_FREE(GETP(NEXT_FREE(hare)))) == NULL) {
      return 0;
    }

    hare = GETP(NEXT_FREE(GETP(NEXT_FREE(hare))));
    tortoise = GETP(NEXT_FREE(tortoise));
  }
  return 1;
}
*/
static void *find_fit(size_t asize) {
  void *bp;
  //  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
  //  if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
  //    return bp;
  for (bp = free_head; bp != NULL; bp = GETP(NEXT_FREE(bp))) {
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
      return bp;
    }
  }
  return NULL;
}


/*
static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}
*/
/*
 * checkheap - Minimal check of the heap for consistency
 */
void mm_checkheap(int lineno)
{
  lineno++;
  /*
  lineno++;
  printf("%d\n", lineno);
  char *bp = heap_listp;


  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {

    checkblock(bp);
  }

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
      printf("Bad epilogue header\n");
  */
}

