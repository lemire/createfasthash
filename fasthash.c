#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <memory.h>
#include <time.h>
#include <math.h>

uint64_t hash( const void *p, size_t len )
{
  uint64_t r8 = UINT64_C(0x1591aefa5e7e5a17);
  uint64_t r9 = UINT64_C(0x2bb6863566c4e761);
  uint64_t                     rax = len ^ r8;
  uint64_t                     rcx = r9;
  uint64_t                     rdx;
#define bswap( r ) \
  __asm__ __volatile__ ( "bswapq %0" : "+r" (r) : : )
#define mul128( a, d, r ) \
  __asm__ __volatile__ ( "mulq %2" : "+a" (a), "=d" (d) : "r" (r) : )

  while ( len >= 16 ) {
    rax = ( rax ^ ((uint64_t*) p)[ 0 ] ) * r8;
    rcx = ( rcx ^ ((uint64_t*) p)[ 1 ] ) * r9;
    bswap( rax );
    bswap( rcx );
    p = &((uint64_t*) p)[ 2 ];
    len -= 16;
  }
  if ( len != 0 ) {
    if ( ( len & 8 ) != 0 ) {
      rdx = 0;
      rax ^= ((uint64_t*) p)[ 0 ];
      p = &((uint64_t*) p)[ 1 ];
    }
    if ( ( len & 4 ) != 0 ) {
      rdx = ((unsigned int *) p)[ 0 ];
      p = &((unsigned int *) p)[ 1 ];
    }
    if ( ( len & 2 ) != 0 ) {
      rdx = ( rdx << 16 ) | ((uint16_t *) p)[ 0 ];
      p = &((uint16_t *) p)[ 1 ];
    }
    if ( ( len & 1 ) != 0 ) {
      rdx = ( rdx << 8 ) | ((uint8_t *) p)[ 0 ];
    }
    rcx ^= rdx;
  }
  mul128( rax, rdx, r8 );
  rcx = ( rcx * r9 ) + rdx;
  rax ^= rcx;
  mul128( rax, rdx, r8 );
  rcx = ( rcx * r9 ) + rdx;
  rax ^= rcx;

  return ( rax >> 32 ) ^ rax;
}

/* check for problems with nulls and odd-sized hashes */
static void simple_string_test(void)
{
	uint8_t buf[8];
	uint64_t i;

	memset(buf, 0, 8);

	printf("These should all be different\n");
	for (i=0; i<8; i++)
	{
		printf("%lld  0-byte strings, hash is %llx\n", i, hash(buf, i));
	}

	memset(buf, 42, 8);
	printf("These should also all be different\n");
	for (i=1; i<8; i++)
	{
		printf("%lld  42-byte strings, hash is %llx\n", i, hash(buf, i));
	}

	printf("These should also all be different\n");
	for (i=1; i<8; i++)
	{
		buf[i] += i;
	}

	for (i=1; i<8; i++)
	{
		printf("%lld  42+-byte strings, hash is %llx\n", i, hash(buf, i));
	}
}


/* check that every input bit changes every output bit half the time */
#define MAXPAIR 80
#define MAXLEN 100
static void avalanche(void)
{
	uint8_t qa[MAXLEN+1], qb[MAXLEN+2], *a = &qa[0], *b = &qb[1];
	uint64_t c, d, i, j = 0, k, l, z;
	uint64_t e, f, g, h;
	uint64_t x, y;
	uint64_t hlen;

	printf("No more than %d trials should ever be needed \n",MAXPAIR/2);
	for (hlen = 0; hlen < MAXLEN; ++hlen)
	{
		z = 0;

		/* For each input byte, */
		for (i = 0; i < hlen; ++i)
		{
			/* for each input bit, */
			for (j = 0; j < 8; ++j)
			{
				e=f=g=h=x=y=~(uint64_t)0;

				/* check that every output bit is affected by that input bit */
				for (k = 0; k < MAXPAIR; k += 2)
				{
					/* keys have one bit different */
					for (l=0; l<hlen+1; ++l)
					{
						a[l] = b[l] = 0;
					}

					/* have a and b be two keys differing in only one bit */
					a[i] ^= (k<<j);
					a[i] ^= (k>>(8-j));
					c = hash(a, hlen);
					b[i] ^= ((k+1)<<j);
					b[i] ^= ((k+1)>>(8-j));
					d = hash(b, hlen);

					e &= c^d;
					f &= ~(c^d);
					g &= c;
					h &= ~c;
					x &= d;
					y &= ~d;

					if (!(e|f|g|h|x|y)) break;
				}
				if (k > z) z = k;
				if (k == MAXPAIR)
				{
					printf("Some bit didn't change: ");
					printf("%.8llx %.8llx %.8llx %.8llx %.8llx %.8llx  ", e,f,g,h,x,y);
					printf("i %lld j %lld len %lld\n",i,j,hlen);
				}
				if (z == MAXPAIR) goto done;
			}
		}

done:
		if (z < MAXPAIR)
		{
			printf("Mix success  %2lld bytes ",i);
			printf("required  %lld  trials\n",z/2);
		}
	}
	printf("\n");
}

/* Modify the k-th bit */
static void modify_bit(uint8_t *a, unsigned k)
{
	/* XOR the appropriate byte in the bitstring with the right bit */
	a[k/8] ^= 1 << (k&7);
}

static void corr_1st_order(uint64_t trials, int size)
{
	int i, j, k;

	uint8_t *state = calloc(size, 1);
	uint8_t *save = calloc(size, 1);

	uint64_t inb, outb;

	int *t = calloc(sizeof(int) * 64 * size * 8, 1);

	double x, y, ssq = 0;
	double maxt = 50.0, mint = 50.0;
	double sfactor = 4.0*64/sqrt(trials);

	srandom( time(NULL));

	for (i = 0; i < trials; i++)
	{
		for (j = 0; j < size; j++)
		{
			state[j] = random();
		}

		memcpy(save, state, size);

		inb = hash(state, size);

		for (k = 0; k < 8 * size; k++)
		{
			memcpy(state, save, size);

			modify_bit(state, k);

		    outb = hash(state, size) ^ inb;

		    for (j = 0; j < 64; j++)
		    {
		        t[k * 64 + j] += outb & 1;
				outb /= 2;
		    }
		}
	}

	for (i = 0; i < 8 * size; i++)
	{
		for (j = 0; j < 64; j++)
		{
			x = t[i * 64 + j] * 100.0 / trials;
			if (x > maxt) maxt = x;
			if (x < mint) mint = x;

			y = fabs(x - 50.0);
			if (y > sfactor) printf("Bad value %f (%d %d)\n", x, i, j);

			ssq += (x-50)*(x-50);
		}
	}

	ssq /= (64 * 8 * size);

	printf("Max %f Min %f Variance %f sfactor %f\n", maxt, mint, ssq, sfactor);

	free(t);
	free(state);
	free(save);
}

static void corr_2nd_order(uint64_t trials, int size)
{
	int i, j, k, l;

	uint8_t *state = calloc(size, 1);
	uint8_t *save = calloc(size, 1);

	uint64_t inb, outb, o1, o2;

	int *t = calloc(sizeof(int) * 64 * 63 * size * 8, 1);

	double x, y, ssq = 0;
	double maxt = 50.0, mint = 50.0;
	double sfactor = 3.0*64/sqrt(trials);

	srandom(time(NULL));

	for (i = 0; i < trials; i++)
	{
		for (j = 0; j < size; j++)
		{
			state[j] = random();
		}

		memcpy(save, state, size);

		inb = hash(state, size);

		for (k = 0; k < 8 * size; k++)
		{
			memcpy(state, save, size);

			modify_bit(state, k);

		    outb = hash(state, size) ^ inb;

			o1 = outb;

		    for (j = 0; j < 64; j++)
		    {
				o2 = o1;
				for (l = j + 1; l < 64; l++)
				{
					o2 /= 2;
					t[k * 64 * 63 + j * 63 + l - 1] += (o1 ^ o2) & 1;
				}

				o1 /= 2;
		    }
		}
	}

	for (i = 0; i < 8 * size; i++)
	{
		for (j = 0; j < 64; j++)
		{
			for (k = j + 1; k < 64; k++)
			{
				x = t[i * 64 * 63 + j * 63 + k - 1] * 100.0 / trials;
				if (x > maxt) maxt = x;
				if (x < mint) mint = x;

				y = fabs(x - 50.0);
				if (y > sfactor) printf("Bad value %f (%d %d %d)\n", x, i, j, k);

				ssq += (x-50)*(x-50);
			}
		}
	}

	ssq /= (64 * 63 * 8 * size);

	printf("Max %f Min %f Variance %f sfactor %f\n", maxt, mint, ssq, sfactor);

	free(t);
	free(state);
	free(save);
}

static void benchmark(void)
{
	int size = 1 << 28;
	uint8_t *buf = calloc(size, 1);
	uint64_t result = 0;

	int i;

	for (i = 0; i < size / 8; i++)
	{
		result += hash(buf, 8);
	}

	for (i = 0; i < size / 32; i++)
	{
		result += hash(buf, 32);
	}

	for (i = 0; i < size / 1024; i++)
	{
		result += hash(buf, 1024);
	}

	for (i = 0; i < size / (1 << 16); i++)
	{
		result += hash(buf, 1 << 16);
	}

	for (i = 0; i < size / (1 << 22); i++)
	{
		result += hash(buf, 1 << 22);
	}

	printf("Result : %llu\n", result);
}


int main() {
  benchmark();
  simple_string_test();
  avalanche();
  corr_1st_order(1000000,32);
  corr_2nd_order(1000000,32);
}
