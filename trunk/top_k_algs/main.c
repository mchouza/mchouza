#include <assert.h>
#include <memory.h>
#include <stdio.h>
#include <time.h>

#include "top_k.h"

typedef enum
{
    cp_alg,
    ip_alg
} alg_type_t;

typedef struct
{
    alg_type_t alg_type;
    void (*alg_fun)(void);
    const char *alg_name;
} alg_entry_t;

typedef struct
{
    void (*init)(int *, size_t, size_t);
    int (*test)(int *, int *, size_t, size_t);
    size_t n;
    size_t k;
    const char *test_name;
} test_entry_t; 

#define ASIZE(a) (sizeof(a) / sizeof(a[0]))

#define IP_ALG_ENTRY(alg_fun) {ip_alg, (void(*)(void))(alg_fun), #alg_fun}
#define CP_ALG_ENTRY(alg_fun) {cp_alg, (void(*)(void))(alg_fun), #alg_fun}
#define TEST_ENTRY(init, test, n, k, name) {init ## _init, test ## _test, n, k, name}

#define MEASURING_TIME 1

static int int_cmp(const void *p, const void *q)
{
    int a = *(const int *)p, b = *(const int *)q;
    return (a > b) ? 1 : ((a < b) ? -1 : 0);
}

static void random_init(int *a, size_t n, size_t k)
{
    size_t i;
    srand((int)a ^ n ^ k);
    for (i = 0; i < n; i++)
        a[i] = rand();
}

static void seq_init(int *a, size_t n, size_t k)
{
    size_t i;
    for (i = 0; i < n; i++)
        a[i] = i;
}

static void downseq_init(int *a, size_t n, size_t k)
{
    size_t i;
    for (i = 0; i < n; i++)
        a[i] = n - 1 - i;
}

static int seq_test(int *a, int *tk, size_t n, size_t k)
{
    size_t i;
    qsort(tk, k, sizeof(int), int_cmp);
    for (i = 0; i < k; i++)
        if (tk[i] != n - k + i)
            return 0;
    return 1;
}

static int random_test(int *a, int *tk, size_t n, size_t k)
{
    size_t i;
    int *a2;
    srand((int)a ^ n ^ k);
    a2 = malloc(n * sizeof(int));
    for (i = 0; i < n; i++)
        a2[i] = rand();
    qsort(a2, n, sizeof(int), int_cmp);
    qsort(tk, k, sizeof(int), int_cmp);
    for (i = 0; i < k; i++)
        if (tk[i] != a2[n - k + i])
            break;
    free(a2);
    return (i == k);
}

static int do_test(void (*f)(void), alg_type_t alg_type, size_t n, size_t k, 
                   void (*init)(int *a, size_t n, size_t k),
                   int (*test)(int *a, int *tk, size_t n, size_t k))
{
    int *a;
    int *tk;
    int ok;

    a = malloc(n * sizeof(int));
    if (alg_type == cp_alg)
        tk = malloc(k * sizeof(int));

    init(a, n, k);

    if (alg_type == cp_alg)
        ((top_k_cp_t *)f)(tk, k, a, n);
    else if (alg_type == ip_alg)
        tk = ((top_k_ip_t *)f)(a, n, k);
    else
        assert(0);

    ok = test(a, tk, n, k);
    
    if (alg_type == cp_alg)
        free(tk);
    free(a);

    return ok;
}

static double do_timing(void (*f)(void), alg_type_t alg_type, size_t n, 
                        size_t k, void (*init)(int *a, size_t n, size_t k))
{
    clock_t start, end;
    int *a;
    int *b;
    int *tk;
    size_t i, num_iters = 1;

    a = malloc(n * sizeof(int));
    if (alg_type == ip_alg)
        b = malloc(n * sizeof(int));
    if (alg_type == cp_alg)
        tk = malloc(k * sizeof(int));

    init(a, n, k);

    end = start = 0;
    while (end - start < MEASURING_TIME * CLOCKS_PER_SEC)
    {
        if (alg_type == cp_alg)
        {
            start = clock();
            for (i = 0; i < num_iters; i++)
                ((top_k_cp_t *)f)(tk, k, a, n);
            end = clock();
        }
        else if (alg_type == ip_alg)
        {
            clock_t start2, end2;
            
            start = clock();
            for (i = 0; i < num_iters; i++)
            {
                memcpy(b, a, n * sizeof(int));
                ((top_k_ip_t *)f)(b, n, k);
            }
            end = clock();

            start2 = clock();
            for (i = 0; i < num_iters; i++)
                memcpy(b, a, n * sizeof(int));
            end2 = clock();

            if (end - start < end2 - start2)
                end = start;
            else
                end -= end2 - start2;
        }
        else
        {
            assert(0);
        }

        num_iters *= 10;
    }
    num_iters /= 10;

    if (alg_type == cp_alg)
        free(tk);
    if (alg_type == ip_alg)
        free(b);
    free(a);

    return (double)(end - start) / CLOCKS_PER_SEC / num_iters;
}

static alg_entry_t algorithms_to_test[] = 
{
    CP_ALG_ENTRY(top_k_nlogn_cp),
    CP_ALG_ENTRY(top_k_nlogk_cp),
    CP_ALG_ENTRY(top_k_n_cp),
    IP_ALG_ENTRY(top_k_nlogn_ip),
    IP_ALG_ENTRY(top_k_n_ip),
    IP_ALG_ENTRY(top_k_n_ip_cpp)
};

static test_entry_t tests[] =
{
    TEST_ENTRY(random, random, 10, 3, "small_random"),
    TEST_ENTRY(seq, seq, 10, 3, "small_seq"),
    TEST_ENTRY(downseq, seq, 10, 3, "small_downseq"),
    TEST_ENTRY(random, random, 1000000, 300, "large_random")
};

#define TIMING_INIT random_init
#define TIMING_START_N 100
#define TIMING_END_N 10000000
#define TIMING_START_K 3
#define TIMING_MULT 10
#define TIMING_ITERS 5

static void run_all_tests(void)
{
    size_t i, j;
    alg_entry_t *ae;
    test_entry_t *te;
    for (i = 0; i < ASIZE(algorithms_to_test); i++)
    {
        for (j = 0; j < ASIZE(tests); j++)
        {
            ae = &algorithms_to_test[i];
            te = &tests[j];
            if (!do_test(ae->alg_fun, ae->alg_type, te->n, te->k, te->init, 
                         te->test))
            {
                printf("Error when doing test '%s' over algorithm '%s'.\n", 
                       te->test_name, ae->alg_name);
                exit(1);
            }
        }
    }
}

static void run_all_timings(void)
{
    size_t n, k, i, j;
    alg_entry_t *ae;
    double time;

    for (i = 0; i < ASIZE(algorithms_to_test); i++)
    {
        ae = &algorithms_to_test[i];
        printf("alg_name: %s\n", ae->alg_name);

        for (n = TIMING_START_N; n <= TIMING_END_N; n *= TIMING_MULT)
        {
            printf("n: %u\n", n);

            for (k = TIMING_START_K; k < n; k *= TIMING_MULT)
            {
                printf("k: %u\n", k);
                printf("times: ");

                for (j = 0; j < TIMING_ITERS; j++)
                {
                    time = do_timing(ae->alg_fun, ae->alg_type, n, k, 
                                     TIMING_INIT);
                    printf("%e ", time);
                }

                printf("\n");
            }
        }
    }
}

int main(void)
{
    run_all_tests();
    run_all_timings();

    return 0;
}
