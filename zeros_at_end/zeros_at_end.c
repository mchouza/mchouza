#include <stdio.h>
#include <string.h>

/* Mariano 1 */
void f1(int* a, size_t n)
{
    size_t i = 0, j;
    for (j = 0; j < n; j++)
        if (a[j])
            a[i++] = a[j];
    for (; i < n; i++)
        a[i] = 0;
}

/* Mariano 2 */
void f2(int* p, size_t n)
{
    int *q, *r;
    for (q = p, r = p + n; q < r; q++)
        if (*q)
            *p++ = *q;
    for (; p < r; p++)
        *p = 0;
}

/* Mariano 3 */
void f3(int* p, size_t n)
{
    int *q = p, *r = p + n;
    while ((r - p) * (r - q ? *q ? (*p++ = *q++) : ++q - p : (*p++ = 0) + 1));
}

/* Mariano 4 */
void f4(int* p, size_t n)
{
    if (n == 0)
        return;
    f4(p + 1, n - 1);
    while (n >= 2)
    {
        if (!p[0] && p[1])
        {
            /* xor swap */
            /* Proof:
               p0' = p0 ^ p1
               p1f = p1 ^ p0'
                   = p1 ^ p0 ^ p1
                   = p0
               p0f = p0' ^ p1f
                   = p0 ^ p1 ^ p0
                   = p1
            */
            p[0] ^= p[1];
            p[1] ^= p[0];
            p[0] ^= p[1];
        }
        p++;
        n--;
    }
}

/* Demian 1 */
void f5(int* a, size_t n)
{
	size_t i;
    size_t top = 0;
	for (i = 0; i < n; ++i)
		if (a[i] != 0)
			a[top++] = a[i];

	for (i = top; i < n; ++i)
		a[i] = 0;
}

/* aux function for Demian 2 */
void swap(int* a, int i, int j)
{
    int t;
    t = a[i];
    a[i] = a[j];
    a[j] = t;
}

/* Demian 2 */
void f6(int* a, size_t n)
{
	size_t top = 0;
    size_t i;
	for (i = 0; i < n; ++i)
		if (a[i] != 0)
			swap(a, i, top++);
}

/* aux function for Guille 1 */
void swap2(int* x, int* y){
	int z= *x;
	*x= *y;
	*y= z;
}

/* Guille 1 */
void f7(int* a, size_t n)
{
	if (n <= 1) return;

	if (!(*a)){
		if (*(a+1)){
			swap2(a, a+1);
		}
	}

	f7(a+1, n-1);
}

/* Mariano 5 */
void f8(int* a, size_t n)
{
    size_t j;
    for (j = 0; j < n; j++)
    {
        if (a[j])
            a[0] = a[j], a++, j--, n--;
    }
    for (j = 0; j < n; j++)
        a[j] = 0;
}

int t1a[] = {5, 0, 4, 0, 0, 3, 0, 0, 0, 2};
int t1b[] = {5, 4, 3, 2, 0, 0, 0, 0, 0, 0};
int t2a[] = {0, 0, 0};
int t2b[] = {0, 0, 0};
int t3a[] = {4, 5, 6};
int t3b[] = {4, 5, 6};
int t4a[] = {0};
int t4b[] = {0};
int t5a[] = {0, 3, 2, 1, 0};
int t5b[] = {3, 2, 1, 0, 0};
int t6a[] = {0, 0, 0, 1, 2, 3, 0, 4};
int t6b[] = {1, 2, 3, 4, 0, 0, 0, 0};

int test(void (*f)(int*, size_t), int* ta, int* tb, size_t n)
{
    int a[1024];
    memcpy(a, ta, n * sizeof(int));
    f(a, n);
    return memcmp(a, tb, n * sizeof(int)) == 0;
}

#define ASIZE(a) (sizeof(a)/sizeof(a[0]))

int main(void)
{
    void (*f[])(int*, size_t) = {f1, f2, f3, f4, f5, f6, f7, f8};
    int* ta[] = {t1a, t2a, t3a, t4a, t5a, t6a};
    int* tb[] = {t1b, t2b, t3b, t4b, t5b, t6b};
    size_t ns[] = {ASIZE(t1a), ASIZE(t2a), ASIZE(t3a), ASIZE(t4a), ASIZE(t5a), ASIZE(t6a)};
    int i, j;

    for (i = 0; i < ASIZE(f); i++)
        for (j = 0; j < ASIZE(ta); j++)
            if (!test(f[i], ta[j], tb[j], ns[j]))
                printf("Failure with f%d, t%da & t%db.\n", i + 1, j + 1, j + 1);
}
