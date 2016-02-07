#define _GNU_SOURCE
#include <limits.h>
#include <smmintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* based on the one included in http://xorshift.di.unimi.it/xorshift128plus.c */
static uint64_t _s[2];
void _seed_random(uint64_t s)
{
    _s[0] = s + 0xA2FFB973E64B0844;
    _s[1] = s + 0xC8FA4CC7BE7EA81E;
}
uint64_t _random(void)
{
    uint64_t s1 = _s[0];
    const uint64_t s0 = _s[1];
    _s[0] = s0;
    s1 ^= s1 << 23; // a
    _s[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5); // b, c
    return _s[1] + s0; 
}

uint8_t *_build_random_correlated_array(size_t arr_size, double p_ii, unsigned seed)
{
    if (p_ii < 1.0 / 256.0)
        return NULL;
    uint8_t *arr = (uint8_t *)malloc(arr_size);
    if (arr == NULL)
        return NULL;
    _seed_random(seed);
    arr[0] = _random() & 0xff;
    for (size_t i = 1; i < arr_size; i++)
    {
        unsigned long r = _random();
        if (r < ULONG_MAX * (p_ii - (1.0 - p_ii) / 256.0))
            arr[i] = arr[i-1];
        else
            arr[i] = r & 0xff;
    }
    return arr;
}

uint8_t *_build_random_indep_array(size_t arr_size, double p, int c, unsigned seed)
{
    uint8_t *arr = (uint8_t *)malloc(arr_size);
    if (arr == NULL)
        return NULL;
    _seed_random(seed);
    for (size_t i = 0; i < arr_size; i++)
    {
        unsigned long r = _random();
        if (r < ULONG_MAX * (p - (1.0 - p) / 256.0))
            arr[i] = c;
        else
            arr[i] = r & 0xff;
    }
    return arr;
}

static uint64_t _get_timestamp(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return 1000000000 * ts.tv_sec + ts.tv_nsec;
}

size_t memcount_naive(const void *s, int c, size_t n)
{
    const uint8_t *b = (const uint8_t *)s;
    size_t count = 0;
    for (size_t i = 0; i < n; i++)
        if (b[i] == c)
            count++;
    return count;
}

size_t memcount_sse(const void *s, int c, size_t n)
{
    size_t nb = n / 16;
    size_t count = 0;
    __m128i ct = _mm_set1_epi32(c * ((~0UL) / 0xff));
    __m128i z = _mm_set1_epi32(0);
    __m128i acr = _mm_set1_epi32(0);
    for (size_t i = 0; i < nb; i++)
    {
        __m128i b = _mm_lddqu_si128((const __m128i *)s + i);
        __m128i cr = _mm_cmpeq_epi8 (ct, b);
        acr = _mm_add_epi8(acr, cr);
        if (i % 0xff == 0xfe)
        {
            acr = _mm_sub_epi8(z, acr);
            __m128i sacr = _mm_sad_epu8(acr, z);
            count += _mm_extract_epi64(sacr, 0);
            count += _mm_extract_epi64(sacr, 1);
            acr = _mm_set1_epi32(0);
        }
    }
    acr = _mm_sub_epi8(z, acr);
    __m128i sacr = _mm_sad_epu8(acr, z);
    count += _mm_extract_epi64(sacr, 0);
    count += _mm_extract_epi64(sacr, 1);
    for (size_t i = nb * 16; i < n; i++)
        if (((const uint8_t *)s)[i] == c)
            count++;
    return count;
}

int main(void)
{
    size_t a1_size = 100 << 20;
    uint8_t *a1 = _build_random_correlated_array(a1_size, 1.0 / 256.0, 0);
    size_t a2_size = (100 << 20) + 35;
    uint8_t *a2 = _build_random_correlated_array(a2_size, 1.0 / 2.0, 0);
    size_t a3_size = (100 << 20) + 21;
    uint8_t *a3 = _build_random_indep_array(a3_size, 1.0 / 256.0, 45, 0);
    size_t a4_size = (100 << 20) + 1;
    uint8_t *a4 = _build_random_indep_array(a4_size, 255.0 / 256.0, 45, 0);
    size_t a5_size = (100 << 20) + 13;
    uint8_t *a5 = _build_random_indep_array(a5_size, 256.0 / 256.0, 45, 0);
    printf("Generated random arrays.\n");
    #define COUNT(arr, fun)\
    {\
        uint64_t start = _get_timestamp();\
        size_t count = fun(arr, 45, arr ## _size);\
        uint64_t end = _get_timestamp();\
        printf("Count of character %u in '%s' using '%s' is: %zu\n", 45, #arr, #fun, count);\
        printf("Elapsed time: %llu ns\n", (unsigned long long)(end - start));\
    }
    #define TIME_MEMCHR(arr)\
    {\
        uint64_t start = _get_timestamp();\
        const void *pos = memchr(arr, 13, arr ## _size);\
        uint64_t end = _get_timestamp();\
        printf("Timing 'memchr()' to get character %d' in '%s'. Result: %p\n", 13, #arr, pos);\
        printf("Elapsed time: %llu ns\n", (unsigned long long)(end - start));\
    }
    #ifdef TEST_NAIVE
    COUNT(a1, memcount_naive);
    COUNT(a1, memcount_naive);
    COUNT(a2, memcount_naive);
    COUNT(a3, memcount_naive);
    COUNT(a4, memcount_naive);
    COUNT(a5, memcount_naive);
    #endif
    #ifdef TEST_MEMCHR
    TIME_MEMCHR(a5);
    TIME_MEMCHR(a5);
    #endif
    #ifdef TEST_SSE
    COUNT(a1, memcount_sse);
    COUNT(a2, memcount_sse);
    COUNT(a3, memcount_sse);
    COUNT(a4, memcount_sse);
    COUNT(a5, memcount_sse);
    #endif
    return 0;
}