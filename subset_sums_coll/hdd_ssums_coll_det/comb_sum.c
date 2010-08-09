#include "bignum.h"
#include "comb_sum.h"
#include "marsaglia.h"
#include <stdlib.h>
#include <string.h>

static bignum_t nums[] =
{
    {0xbb37fe55, 0x485a62ab, 0x00000000},
    {0x1357df5a, 0x7d0e4851, 0x00000000},
    {0x74d07171, 0x7e81e02c, 0x00000000},
    {0xc644ac18, 0x18ef525c, 0x00000000},
    {0xe6177136, 0x20f61d86, 0x00000000},
    {0xa6bc73e1, 0x31adae82, 0x00000000},
    {0x2651e419, 0x201941df, 0x00000000},
    {0x90d82767, 0x3257ca8a, 0x00000000},
    {0x38760842, 0x527459d4, 0x00000000},
    {0xf72e0129, 0x3beb89ae, 0x00000000},
    {0xc2322fae, 0x4ffa7c9e, 0x00000000},
    {0xc1d2de47, 0x48870065, 0x00000000},
    {0x90c8ce39, 0x25e64a91, 0x00000000},
    {0xa18a49d7, 0x5689787d, 0x00000000},
    {0x5e68ae8f, 0x4596a002, 0x00000000},
    {0x302766c5, 0x4390eeec, 0x00000000},
    {0xac8b8b1e, 0x87222686, 0x00000000},
    {0xfbee9a05, 0x808b3e3a, 0x00000000},
    {0x0d77c9ee, 0x52d38b35, 0x00000000},
    {0x75d29425, 0x5db453d8, 0x00000000},
    {0x92f56028, 0x52208b07, 0x00000000},
    {0x41de63e3, 0x5169c549, 0x00000000},
    {0x94f22558, 0x80228f85, 0x00000000},
    {0x8a3a8fb7, 0x821f7298, 0x00000000},
    {0x8b85d856, 0x3459870d, 0x00000000},
    {0x02461f4b, 0x7d506cae, 0x00000000},
    {0x36812b90, 0x2e0f6c0f, 0x00000000},
    {0x910e524b, 0x7fc0ac1c, 0x00000000},
    {0xbc9f6edf, 0x83cfc9e2, 0x00000000},
    {0xdfce4ea3, 0x8aa3fc5b, 0x00000000},
    {0xee8695ac, 0x88b0cd86, 0x00000000},
    {0x775416d2, 0x24f9a6f6, 0x00000000},
    {0xcee5e980, 0x131b51b9, 0x00000000},
    {0x698f2769, 0x0f626251, 0x00000000},
    {0xdad99fc4, 0x6c8842b7, 0x00000000},
    {0x47da3b3b, 0x16409d09, 0x00000000},
    {0x6aa0b57c, 0x60792509, 0x00000000},
    {0xde590857, 0x89402538, 0x00000000},
    {0x5bb4de6d, 0x4249dc7b, 0x00000000},
    {0x65c596b6, 0x6a3205a1, 0x00000000},
    {0x710e55c8, 0x3745c82d, 0x00000000},
    {0x0841d4e4, 0x702b51d6, 0x00000000},
    {0xf367e994, 0x111f4786, 0x00000000},
    {0x3e980d6b, 0x3b46781d, 0x00000000},
    {0x119b5953, 0x6f057f85, 0x00000000},
    {0x39996fc6, 0x14f19016, 0x00000000},
    {0x4146e4c5, 0x59074438, 0x00000000},
    {0x7b56b711, 0x397fd15f, 0x00000000},
    {0xf2a44701, 0x58bb34fb, 0x00000000},
    {0xf7ebc9b5, 0x1fc9d762, 0x00000000},
    {0x29f92138, 0x6cbb8cb5, 0x00000000},
    {0x215936cd, 0x760ae80d, 0x00000000},
    {0xddfcbb0e, 0x68bf7c86, 0x00000000},
    {0xffc18313, 0x3d2cbe1c, 0x00000000},
    {0xd5af065e, 0x7ce0fd2e, 0x00000000},
    {0x834230dd, 0x7eb9af7f, 0x00000000},
    {0x4190b7cf, 0x7e3dbaf3, 0x00000000},
    {0x16c21846, 0x67d216aa, 0x00000000},
    {0x3d5b8aec, 0x497e502c, 0x00000000},
    {0x15e8dd81, 0x18ed6dd9, 0x00000000},
    {0x77c6f44a, 0x529ed5fd, 0x00000000},
    {0xb0830839, 0x2bbd94dc, 0x00000000},
    {0x6f5a9732, 0x59727f29, 0x00000000},
    {0x2eba2b1a, 0x89cb2ecf, 0x00000000},
    {0xb8eabe09, 0x59206a98, 0x00000000},
    {0x59cf2c7d, 0x77f3370a, 0x00000000},
    {0x8b7f8f02, 0x640658ea, 0x00000000},
    {0xd6b846d5, 0x324df2e3, 0x00000000},
    {0xdd754107, 0x347f614d, 0x00000000},
    {0x01ec5f47, 0x53726ff8, 0x00000000},
};

static bignum_t* all_sums_by_word_and_pos[5];

void comb_init(void)
{
    int i, j;
    byte comb_set[10]; /* ceil(70/16)*16 = 80 */

    /* reserves memory for the fast sum buffers */
    for (i = 0; i < 5; i++)
        all_sums_by_word_and_pos[i] = malloc((1 << 16) * sizeof(bignum_t));

    /* fills the buffers */
    for (i = 0; i < 5; i++)
    {
        memset(comb_set, 0, sizeof(comb_set));
        for (j = 0; j < 1 << 16; j++)
        {
            ((uint16_t*)comb_set)[i] = j;
            comb_sum(&all_sums_by_word_and_pos[i][j], comb_set);
        }
    }
}

void comb_free(void)
{
    int i;
    for (i = 0; i < 5; i++)
    {
        if (all_sums_by_word_and_pos[i])
        {
            free(all_sums_by_word_and_pos[i]);
            all_sums_by_word_and_pos[i] = NULL;
        }
    }
}

void comb_sum(bignum_t* sum, const byte* comb_set)
{
    int i;
    bignum_clear(sum);
    for (i = 0; i < 70; i++)
        if (comb_set[i / 8] & (1 << (i % 8)))
            bignum_add(sum, &nums[i]);
}

void comb_fast_sum(bignum_t* sum, const byte* comb_set)
{
    int i;
    bignum_copy(sum, &all_sums_by_word_and_pos[0][*(uint16_t*)comb_set]);
    for (i = 1; i < 5; i++)
        bignum_add(sum, &all_sums_by_word_and_pos[i][((uint16_t*)comb_set)[i]]);
}

#if 0

/* correctness test */

#include <string.h>
#include <stdio.h>

#define TEST_COMB_SUM(comb, sum_str)\
{\
    byte comb_set[] = comb;\
    char buf[80];\
    bignum_t sum;\
    comb_sum(&sum, comb_set);\
    bignum_sprint(buf, &sum);\
    if (strcmp(buf, sum_str))\
        printf("Error at %d in %s.\n", __LINE__, __FILE__);\
}

#define TEST_COMB_FSUM(comb, sum_str)\
{\
    byte comb_set[] = comb;\
    char buf[80];\
    bignum_t sum;\
    comb_fast_sum(&sum, comb_set);\
    bignum_sprint(buf, &sum);\
    if (strcmp(buf, sum_str))\
        printf("Error at %d in %s.\n", __LINE__, __FILE__);\
}

int main(void)
{
    TEST_COMB_SUM("\x03\x00\xf0\x00\x00\x00\x00\x00\x01",
                  "0x00000002c45568047b7b14d2");
    TEST_COMB_SUM("\xf3\xe7\x7f\xfe\x9f\xff\xbd\xff\x37",
                  "0x000000132d3993b60360b828");
    TEST_COMB_SUM("\xad\xbd\xde\xff\xfb\xff\xbb\xf7\x2d",
                  "0x0000001250634400f9c20229");
    TEST_COMB_SUM("\xf6\xfb\x8a\xf5\xba\xbc\x59\xb3\x0f",
                  "0x0000000e897a48b08371a7de");
    TEST_COMB_SUM("\x05\x40\x33\x02\x27\x00\x21\x87\x1e",
                  "0x00000007df49486f4ff7735c");
    TEST_COMB_SUM("\x04\x00\x81\x06\x90\x08\x00\x52\x0c",
                  "0x00000004e34cac705377aa57");
    TEST_COMB_SUM("\x10\x0c\x08\x90\xba\x80\x12\x0b\x02",
                  "0x00000005727d4a458d556615");
    TEST_COMB_SUM("\xf1\xd0\xa1\x42\x82\x89\x31\x51\x3a",
                  "0x000000087df3a1c78b4fba98");
    TEST_COMB_SUM("\x00\x00\x00\x00\x80\x80\x00\x00\x00",
                  "0x00000000a3b1d700e11c4dc7");
    TEST_COMB_SUM("\xbf\xff\xff\xff\xff\xf5\xff\xff\x3f",
                  "0x00000015b888c83418072182");
    TEST_COMB_SUM("\x94\x15\x90\x31\x00\x22\x40\x07\x20",
                  "0x000000063630a50b6b799b3e");
    TEST_COMB_SUM("\xaf\x1f\x0c\xa4\x54\x76\xca\xef\x16",
                  "0x0000000c02cf5161ef17427e");
    TEST_COMB_SUM("\x00\x00\x00\x00\x26\x68\x04\x10\x14",
                  "0x00000003064a3398e6ef1705");
    TEST_COMB_SUM("\xbf\xf7\x1b\xdf\xd7\xb7\x5e\xff\x1a",
                  "0x000000109146ee1decac1702");
    TEST_COMB_SUM("\x0c\x05\xc0\xb1\x82\x7f\x9b\x9e\x1b",
                  "0x0000000aa2e4848e3fe98ac1");
    TEST_COMB_SUM("\xfb\x1b\x3b\xbf\x7c\xef\xff\x7f\x3b",
                  "0x000000110e99540998db17e9");
    TEST_COMB_SUM("\x06\x01\x25\x04\x00\x00\x42\x40\x02",
                  "0x000000041583f02b89c5d14e");
    TEST_COMB_SUM("\x20\x02\x00\x20\x40\x00\x08\x00\x00",
                  "0x00000001b091f915fac6d8e7");
    TEST_COMB_SUM("\x68\x98\x5a\x4d\x30\xb6\x42\xd0\x2a",
                  "0x0000000930c74d0b12740c95");
    TEST_COMB_SUM("\x57\xfa\x8c\xca\xa2\xae\x13\x45\x14",
                  "0x0000000a953673128d09ec0b");
    TEST_COMB_SUM("\x40\x05\x9f\x99\x7b\x10\x00\xc1\x20",
                  "0x000000083495cdffd2a15a89");

    comb_init();

    TEST_COMB_FSUM("\x03\x00\xf0\x00\x00\x00\x00\x00\x01",
                   "0x00000002c45568047b7b14d2");
    TEST_COMB_FSUM("\xf3\xe7\x7f\xfe\x9f\xff\xbd\xff\x37",
                   "0x000000132d3993b60360b828");
    TEST_COMB_FSUM("\xad\xbd\xde\xff\xfb\xff\xbb\xf7\x2d",
                   "0x0000001250634400f9c20229");
    TEST_COMB_FSUM("\xf6\xfb\x8a\xf5\xba\xbc\x59\xb3\x0f",
                   "0x0000000e897a48b08371a7de");
    TEST_COMB_FSUM("\x05\x40\x33\x02\x27\x00\x21\x87\x1e",
                   "0x00000007df49486f4ff7735c");
    TEST_COMB_FSUM("\x04\x00\x81\x06\x90\x08\x00\x52\x0c",
                   "0x00000004e34cac705377aa57");
    TEST_COMB_FSUM("\x10\x0c\x08\x90\xba\x80\x12\x0b\x02",
                   "0x00000005727d4a458d556615");
    TEST_COMB_FSUM("\xf1\xd0\xa1\x42\x82\x89\x31\x51\x3a",
                   "0x000000087df3a1c78b4fba98");
    TEST_COMB_FSUM("\x00\x00\x00\x00\x80\x80\x00\x00\x00",
                   "0x00000000a3b1d700e11c4dc7");
    TEST_COMB_FSUM("\xbf\xff\xff\xff\xff\xf5\xff\xff\x3f",
                   "0x00000015b888c83418072182");
    TEST_COMB_FSUM("\x94\x15\x90\x31\x00\x22\x40\x07\x20",
                   "0x000000063630a50b6b799b3e");
    TEST_COMB_FSUM("\xaf\x1f\x0c\xa4\x54\x76\xca\xef\x16",
                   "0x0000000c02cf5161ef17427e");
    TEST_COMB_FSUM("\x00\x00\x00\x00\x26\x68\x04\x10\x14",
                   "0x00000003064a3398e6ef1705");
    TEST_COMB_FSUM("\xbf\xf7\x1b\xdf\xd7\xb7\x5e\xff\x1a",
                   "0x000000109146ee1decac1702");
    TEST_COMB_FSUM("\x0c\x05\xc0\xb1\x82\x7f\x9b\x9e\x1b",
                   "0x0000000aa2e4848e3fe98ac1");
    TEST_COMB_FSUM("\xfb\x1b\x3b\xbf\x7c\xef\xff\x7f\x3b",
                   "0x000000110e99540998db17e9");
    TEST_COMB_FSUM("\x06\x01\x25\x04\x00\x00\x42\x40\x02",
                   "0x000000041583f02b89c5d14e");
    TEST_COMB_FSUM("\x20\x02\x00\x20\x40\x00\x08\x00\x00",
                   "0x00000001b091f915fac6d8e7");
    TEST_COMB_FSUM("\x68\x98\x5a\x4d\x30\xb6\x42\xd0\x2a",
                   "0x0000000930c74d0b12740c95");
    TEST_COMB_FSUM("\x57\xfa\x8c\xca\xa2\xae\x13\x45\x14",
                   "0x0000000a953673128d09ec0b");
    TEST_COMB_FSUM("\x40\x05\x9f\x99\x7b\x10\x00\xc1\x20",
                   "0x000000083495cdffd2a15a89");

    comb_free();

    return 0;
}

#endif

#if 0

/* speed test */

#include "timer.h"
#include <stdio.h>

#define TEST_COMB_SUM(comb)\
{\
    byte comb_set[] = comb;\
    comb_sum(&sum, comb_set);\
}

#define TEST_COMB_FSUM(comb)\
{\
    byte comb_set[] = comb;\
    comb_fast_sum(&sum, comb_set);\
}

int main(void)
{
    bignum_t sum;
    int i;

    comb_init();

    timer_reset();

    for (i = 0; i < 1000; i++)
    {
        TEST_COMB_SUM("\xf3\xe7\x7f\xfe\x9f\xff\xbd\xff\x37");
        TEST_COMB_SUM("\xad\xbd\xde\xff\xfb\xff\xbb\xf7\x2d");
        TEST_COMB_SUM("\xf6\xfb\x8a\xf5\xba\xbc\x59\xb3\x0f");
        TEST_COMB_SUM("\x05\x40\x33\x02\x27\x00\x21\x87\x1e");
        TEST_COMB_SUM("\x04\x00\x81\x06\x90\x08\x00\x52\x0c");
        TEST_COMB_SUM("\x10\x0c\x08\x90\xba\x80\x12\x0b\x02");
        TEST_COMB_SUM("\xf1\xd0\xa1\x42\x82\x89\x31\x51\x3a");
        TEST_COMB_SUM("\x00\x00\x00\x00\x80\x80\x00\x00\x00");
        TEST_COMB_SUM("\xbf\xff\xff\xff\xff\xf5\xff\xff\x3f");
        TEST_COMB_SUM("\x94\x15\x90\x31\x00\x22\x40\x07\x20");
        TEST_COMB_SUM("\xaf\x1f\x0c\xa4\x54\x76\xca\xef\x16");
        TEST_COMB_SUM("\x00\x00\x00\x00\x26\x68\x04\x10\x14");
        TEST_COMB_SUM("\xbf\xf7\x1b\xdf\xd7\xb7\x5e\xff\x1a");
        TEST_COMB_SUM("\x0c\x05\xc0\xb1\x82\x7f\x9b\x9e\x1b");
        TEST_COMB_SUM("\xfb\x1b\x3b\xbf\x7c\xef\xff\x7f\x3b");
        TEST_COMB_SUM("\x06\x01\x25\x04\x00\x00\x42\x40\x02");
        TEST_COMB_SUM("\x20\x02\x00\x20\x40\x00\x08\x00\x00");
        TEST_COMB_SUM("\x68\x98\x5a\x4d\x30\xb6\x42\xd0\x2a");
        TEST_COMB_SUM("\x57\xfa\x8c\xca\xa2\xae\x13\x45\x14");
        TEST_COMB_SUM("\x40\x05\x9f\x99\x7b\x10\x00\xc1\x20");
    }

    printf("Elapsed time: %fs\n", timer_elapsed());

    timer_reset();

    for (i = 0; i < 1000; i++)
    {
        TEST_COMB_FSUM("\xf3\xe7\x7f\xfe\x9f\xff\xbd\xff\x37");
        TEST_COMB_FSUM("\xad\xbd\xde\xff\xfb\xff\xbb\xf7\x2d");
        TEST_COMB_FSUM("\xf6\xfb\x8a\xf5\xba\xbc\x59\xb3\x0f");
        TEST_COMB_FSUM("\x05\x40\x33\x02\x27\x00\x21\x87\x1e");
        TEST_COMB_FSUM("\x04\x00\x81\x06\x90\x08\x00\x52\x0c");
        TEST_COMB_FSUM("\x10\x0c\x08\x90\xba\x80\x12\x0b\x02");
        TEST_COMB_FSUM("\xf1\xd0\xa1\x42\x82\x89\x31\x51\x3a");
        TEST_COMB_FSUM("\x00\x00\x00\x00\x80\x80\x00\x00\x00");
        TEST_COMB_FSUM("\xbf\xff\xff\xff\xff\xf5\xff\xff\x3f");
        TEST_COMB_FSUM("\x94\x15\x90\x31\x00\x22\x40\x07\x20");
        TEST_COMB_FSUM("\xaf\x1f\x0c\xa4\x54\x76\xca\xef\x16");
        TEST_COMB_FSUM("\x00\x00\x00\x00\x26\x68\x04\x10\x14");
        TEST_COMB_FSUM("\xbf\xf7\x1b\xdf\xd7\xb7\x5e\xff\x1a");
        TEST_COMB_FSUM("\x0c\x05\xc0\xb1\x82\x7f\x9b\x9e\x1b");
        TEST_COMB_FSUM("\xfb\x1b\x3b\xbf\x7c\xef\xff\x7f\x3b");
        TEST_COMB_FSUM("\x06\x01\x25\x04\x00\x00\x42\x40\x02");
        TEST_COMB_FSUM("\x20\x02\x00\x20\x40\x00\x08\x00\x00");
        TEST_COMB_FSUM("\x68\x98\x5a\x4d\x30\xb6\x42\xd0\x2a");
        TEST_COMB_FSUM("\x57\xfa\x8c\xca\xa2\xae\x13\x45\x14");
        TEST_COMB_FSUM("\x40\x05\x9f\x99\x7b\x10\x00\xc1\x20");
    }

    printf("Elapsed time: %fs\n", timer_elapsed());

    timer_reset();

    for (i = 0; i < 1000000; i++)
    {
        byte comb[12];
        ((uint32_t*)comb)[0] = get_random();
        ((uint32_t*)comb)[1] = get_random();
        ((uint32_t*)comb)[2] = get_random() & ((1 << (70 - 64)) - 1);

        comb_sum(&sum, comb);
    }

    printf("Elapsed time: %fs\n", timer_elapsed());

    timer_reset();

    for (i = 0; i < 1000000; i++)
    {
        byte comb[12];
        ((uint32_t*)comb)[0] = get_random();
        ((uint32_t*)comb)[1] = get_random();
        ((uint32_t*)comb)[2] = get_random() & ((1 << (70 - 64)) - 1);

        comb_fast_sum(&sum, comb);
    }

    printf("Elapsed time: %fs\n", timer_elapsed());

    bignum_print(&sum);

    comb_free();

    return 0;
}

#endif
