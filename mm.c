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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*basic numbers for size*/
#define Wsize 4
#define ListSize 16

// Group a size and allocated bit into a word
#define Group(size, alloc) ((size) | (alloc))

// Read and write a word at address p in unsigned integer
#define Get(p)            (*(unsigned int *)(p))
#define Put(p, val) (*(unsigned int *)(p) = (val))
#define Set(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Read the size and allocation bit of address
#define Size(p)  (Get(p) & ~0x7)
#define Alloc(p) (Get(p) & 0x1)

//Address of header & footer
#define HP(ptr) ((char *)(ptr) - Wsize)
#define FP(ptr) ((char *)(ptr) + Size(HP(ptr)) - ALIGNMENT)

//Address of next adjacent blocks
#define NextAdj(ptr) ((char *)(ptr) + Size((char *)(ptr) - Wsize))
#define PrevAdj(ptr) ((char *)(ptr) - Size((char *)(ptr) - ALIGNMENT))

// Address of free block's previous and next entries 
#define Next(ptr) ((char *)(ptr) + Wsize)
#define Prev(ptr) ((char *)(ptr))

// Address of free block's previous and next block on the segregated list 
#define NextSG(ptr) (*(char **)(Next(ptr)))
#define PrevSG(ptr) (*(char **)(ptr))

/*Max Min function for comparing values in macro*/
#define Max(a, b) ((a) > (b) ? (a) : (b)) 
#define Min(a, b) ((a) < (b) ? (a) : (b)) 

void *SG_Lists[ListSize];



static void insert(void *ptr, size_t size);
static void delete(void *ptr);
static void *coalesce(void *ptr);
static void *split(void *ptr, size_t size);
static void *extend_heap(size_t size);


static void insert(void *ptr, size_t size)
{
	int list = 0;
	void *insert = NULL;

	while ((list < ListSize - 1) && (size > 1))
	{
		size >>=1;
		list++;
	}

	/*search the sg list to find fitting size*/
	void *position = ptr;
	position = SG_Lists[list];
	while ((position != NULL) && (size > Size(HP(position))))
	{
		insert = position;
		position = NextSG(position);
	}
	if (position == NULL)
	{
		if (insert != NULL)
		{
			Set(Prev(ptr), NULL);
			Set(Next(ptr), insert);
			Set(Prev(insert), ptr);
		}
		else
		{
			Set(Prev(ptr), NULL);
			Set(Next(ptr), NULL);
			SG_Lists[list] = ptr;
		}
	}
	else
	{
		if (insert == NULL)
		{
			Set(Next(position), ptr);
			Set(Prev(ptr), position);
			Set(Next(ptr), NULL);
			SG_Lists[list] = ptr;
		}
		else
		{
			Set(Next(position), ptr);
			Set(Prev(ptr), position);
			Set(Next(ptr), insert);
			Set(Prev(insert), ptr);
		}
	}
	return;
}

static void delete(void *ptr)
{
	int list = 0;
	size_t size =Size(HP(ptr));

	/*search the sg list to find fitting size*/
	while ((list < ListSize - 1) && (size > 1))
	{
		size >>=1;
		list++;
	}

	if (PrevSG(ptr) == NULL)
	{
		if (NextSG(ptr) == NULL)
			SG_Lists[list] = NULL;
		else
			Set(Prev(NextSG(ptr)), NULL);

	}
	else
	{
		if (NextSG(ptr) != NULL)
		{
			Set(Next(PrevSG(ptr)), NextSG(ptr));
			Set(Prev(NextSG(ptr)), PrevSG(ptr));

		}
		else
		{
			Set(Next(PrevSG(ptr)), NULL);
			SG_Lists[list] = PrevSG(ptr);
		}
	}

	return;
}

static void *coalesce(void *ptr)
{
	size_t size = Size(HP(ptr));
	int prev_alloc_bit = Alloc(HP(PrevAdj(ptr)));
	int next_alloc_bit = Alloc(HP(NextAdj(ptr)));

	/*both allocated can't coalesce*/
	if (prev_alloc_bit && next_alloc_bit)
		return ptr;
	/*coalesce with previous adjacent block*/
	else if (!prev_alloc_bit && next_alloc_bit)
	{
		delete(PrevAdj(ptr));
		delete(ptr);
		size += Size(HP(PrevAdj(ptr)));
		Put(HP(PrevAdj(ptr)), Group(size, 0));
		Put(FP(ptr), Group(size, 0));
		ptr = PrevAdj(ptr);
	}
	/*coalesce with next adjacent block*/
	else if (prev_alloc_bit && !next_alloc_bit)
	{
		delete(ptr);
		delete(NextAdj(ptr));
		size += Size(HP(NextAdj(ptr)));
		Put(HP(ptr), Group(size, 0));
		Put(FP(ptr), Group(size, 0));
	}
	/*coalesce with both the previous and next adjacent block*/
	else
	{
		delete(PrevAdj(ptr));
		delete(ptr);
		delete(NextAdj(ptr));
		size += Size(HP(PrevAdj(ptr))) + Size(HP(NextAdj(ptr)));
		Put(HP(PrevAdj(ptr)), Group(size, 0));
		Put(FP(NextAdj(ptr)), Group(size, 0));
		ptr = PrevAdj(ptr);
	}
	insert(ptr, size);
	return ptr;
}
static void *split(void *ptr, size_t size)
{
	size_t chunk_size = Size(HP(ptr));
	assert(chunk_size >= size);
	size_t remain_size = chunk_size - size;
	
	delete(ptr);
	
	/*impliit fragmentation might happen but should folllw alignment*/
	if (remain_size <= ALIGNMENT * 2)
	{
		Put(HP(ptr), Group(chunk_size, 1));
		Put(FP(ptr), Group(chunk_size, 1));
		return ptr;
	}
	
	/*small chunks allocated on the left part of the splitted block for memory efficiency*/
	/*threshold size may depend on trace file*/
	else if (size < 120)
	{
		Put(HP(ptr), Group(size, 1));
		Put(FP(ptr), Group(size, 1));
		Put(HP(NextAdj(ptr)), Group(remain_size, 0));
		Put(FP(NextAdj(ptr)), Group(remain_size, 0));
		insert(NextAdj(ptr), remain_size);
		return ptr;
	}
	
	/*big chunks allocated on the right part of the splitted block for memory efficiency*/
	else
	{
		Put(HP(ptr), Group(remain_size, 0));
		Put(FP(ptr), Group(remain_size, 0));
		Put(HP(NextAdj(ptr)), Group(size, 1));
		Put(FP(NextAdj(ptr)), Group(size, 1));
		insert(ptr, remain_size);
		return NextAdj(ptr);
	}
}
static void *extend_heap(size_t size)
{
	void *ptr;
	size_t unit = ALIGN(size);

	if ((ptr = mem_sbrk(unit)) == (void *)-1)
		return NULL;

	/*mark the extended chunk as free block*/
	Put(HP(ptr), Group(unit, 0));
	Put(FP(ptr), Group(unit, 0));
	Put(HP(NextAdj(ptr)), 1);//mark the end of heap
	/*insert and check if coalesce if possible*/
	insert(ptr, unit);
	ptr = coalesce(ptr);
	return ptr;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	// Allocate memory for the initial empty heap 
	char *heap;
	if ((int)(heap = mem_sbrk(4 * Wsize)) == -1)
		return -1;

	int list;
	/*make an empty segregated list*/
	for (list = 0; list < ListSize; list++)
		SG_Lists[list] = NULL;

	Put(heap + (1 * Wsize), Group(ALIGNMENT, 1)); /* Header for the starting block */
	Put(heap + (2 * Wsize), Group(ALIGNMENT, 1)); /* Footer for the starting block */
	Put(heap + (3 * Wsize), Group(0, 1));     /* Only header for the finishing block */
	Put(heap, 0);

	if (extend_heap((1<<8)) == NULL)
		return -1;
		
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	if (size == 0)
		return NULL;
	
	size_t unit;
	void *ptr = NULL;
	size_t extend;

	if (size <= ALIGNMENT)
		unit = 2 * ALIGNMENT;
	else
		unit = ALIGN(size + ALIGNMENT);
	
	int list = 0;
	size_t search = unit;
	/*find the appropriate size of free block using segregated list*/
	while (list<ListSize)
	{
		if (((search <= 1) && (SG_Lists[list] != NULL)) || (list == ListSize - 1))
		{
			ptr = SG_Lists[list];
			while ((ptr != NULL) && (unit>Size(HP(ptr))))
				ptr = NextSG(ptr);
			if (ptr != NULL)
				break;
		}
		search >>=1;
		list++;
	}
	if (ptr == NULL)
	{
		extend = Max(unit, 1<<12);
		if ((ptr = extend_heap(extend)) == NULL)/*extension failed try another size*/
		{
			extend = Min(unit, 1 << 12);
			if ((ptr = extend_heap(extend)) == NULL)/*extention totally failed*/
			return NULL;
		}
			
	}
	ptr = split(ptr, unit);
	return ptr;
}

void mm_free(void *ptr)
{
	size_t size = Size(HP(ptr));
	Put(HP(ptr), Group(size, 0));
	Put(FP(ptr), Group(size, 0));
	insert(ptr, size);
	coalesce(ptr);
	return;
}

void *mm_realloc(void *ptr, size_t size)
{
	if (size == 0)
		return NULL;

	void *realloc_ptr = ptr;  
	size_t new_size;          
	int extendsize;
	int size_cap;
	
	if (size <= ALIGNMENT)
		new_size = 2 * ALIGNMENT;
	else
		new_size = ALIGN(size + ALIGNMENT);

	/*size is not enough for new size find a new place to reallocate*/
	if (Size(HP(ptr))<new_size)
	{
		/*check if the block is allocated*/
		if (!Alloc(HP(NextAdj(ptr))) || !Size(HP(NextAdj(ptr))))
		{
			size_cap = Size(HP(ptr)) + Size(HP(NextAdj(ptr)));
			if (size_cap < new_size)/*not enough with using next block should extend*/
			{
				extendsize = Max(new_size - size_cap, 1<<12);/*extension failed try another size*/
				if (extend_heap(extendsize) == NULL)
				{
					extendsize = Min(new_size - size_cap, 1 << 12);
					if (extend_heap(extendsize) == NULL)/*extention totally failed*/
						return NULL;
				}
				size_cap += extendsize;
			}
			/*use the next next block*/
			delete(NextAdj(ptr));
			Put(HP(ptr), Group(size_cap, 1));
			Put(FP(ptr), Group(size_cap, 1));
		}
		/*find another place to reallocate*/
		else
		{
			mm_free(ptr);
			realloc_ptr = mm_malloc(new_size);
		}
	}
	return realloc_ptr;

}
