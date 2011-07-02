#include <memory.h>

#include "top_k.h"

#define SWAP(type, a, b) {type swap_temp = a; a = b; b = swap_temp;}

static int int_cmp(const void *p, const void *q)
{
    int a = *(const int *)p, b = *(const int *)q;
    return (a > b) ? 1 : ((a < b) ? -1 : 0);
}

static void minheap_pushdown(int *h, size_t hs, size_t i)
{
    size_t j = 0;
    if (2 * i + 2 < hs)
        j = (h[2 * i + 1] < h[2 * i + 2]) ? 2 * i + 1 : 2 * i + 2;
    else if (2 * i + 1 < hs)
        j = 2 * i + 1;
    if (j != 0 && h[j] < h[i])
    {
        SWAP(int, h[i], h[j]);
        minheap_pushdown(h, hs, j);
    }
}

static void minheap_raise(int *h, size_t i)
{
    if (i == 0)
        return;
    if (h[i] < h[(i - 1) / 2])
    {
        SWAP(int, h[i], h[(i - 1) / 2]);
        minheap_raise(h, (i - 1) / 2);
    }
}

void top_k_nlogn_cp(int *top_k, size_t k, const int *l, size_t n)
{
    int *sl;

    sl = malloc(n * sizeof(int));
    memcpy(sl, l, n * sizeof(int));
    qsort(sl, n, sizeof(int), int_cmp);

    memcpy(top_k, sl + n - k, k * sizeof(int));

    free(sl);
}

void top_k_nlogk_cp(int *top_k, size_t k, const int *l, size_t n)
{
    size_t i;

    for (i = 0; i < k; i++)
    {
        top_k[i] = l[i];
        minheap_raise(top_k, i);
    }

    for (i = k; i < n; i++)
    {
        if (l[i] > top_k[0])
        {
            top_k[0] = l[i];
            minheap_pushdown(top_k, k, 0);
        }
    }
}

void top_k_n_cp(int *top_k, size_t k, const int *l, size_t n)
{
    int *al;

    al = malloc(n * sizeof(int));
    memcpy(al, l, n * sizeof(int));

    top_k_n_ip(al, n, k);

    memcpy(top_k, al + n - k, k * sizeof(int));

    free(al);
}

int *top_k_nlogn_ip(int *l, size_t n, size_t k)
{
    qsort(l, n, sizeof(int), int_cmp);
    return l + n - k;
}

int *top_k_n_ip(int *l, size_t n, size_t k)
{
    size_t lo, hi, pos, i, j;
    int pivot;
   
    lo = 0;
    hi = n;
    pos = n - k;

    while (hi - lo > 1)
    {
        i = lo + 1;
        j = hi - 1;
        pivot = l[lo];

        while (1)
        {
            while (i < hi && l[i] <= pivot)
                i++;
            while (j > lo && l[j] > pivot)
                j--;
            if (i > j)
                break;
            SWAP(int, l[i], l[j]);
        }

        SWAP(int, l[lo], l[j]);

        if (j < pos)
            lo = j + 1;
        else if (j > pos)
            hi = j;
        else
            break;
    }

    return l + n - k;
}
