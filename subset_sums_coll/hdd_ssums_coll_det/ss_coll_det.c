#include "bignum.h"
#include "comb_coll_det.h"
#include "comb_sum.h"
#include "timer.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CCD_LOG_NUM_ELEMS 27
#define COMB_SIZE 10
#define MAX_FPATH 256
#define FPATH_FMT "g:\\subset_sums_data_200_iters_100000000_elems\\%04d.bin"
#define PIVOTS_FPATH "g:\\subset_sums_data_200_iters_100000000_elems\\pivots.bin"
#define NUM_FILES 1000

int comb_sum_cmp(const void* comb1, const void* comb2)
{
    bignum_t op1, op2;
    comb_fast_sum(&op1, (const byte*)comb1);
    comb_fast_sum(&op2, (const byte*)comb2);
    return bignum_cmp(&op1, &op2);
}

FILE* open_comb_file(size_t i)
{
    char fpath[MAX_FPATH];
    sprintf(fpath, FPATH_FMT, i);
    return fopen(fpath, "rb");
}

int main(void)
{
    size_t i, j;
    FILE* pivots_fp;
    FILE* combs_fp;
    comb_coll_det_t* ccd;
    byte comb[COMB_SIZE];
    byte pivot[COMB_SIZE];
    coll_type_t ct;
    byte *other_comb;

    pivots_fp = fopen(PIVOTS_FPATH, "rb");
    ccd = ccd_create(CCD_LOG_NUM_ELEMS, COMB_SIZE);
    comb_init();

    for (i = 0; i < NUM_FILES; i++)
    {
        printf("Processing file %d...", i);
        timer_reset();

        ccd_reset(ccd);
        combs_fp = open_comb_file(i);
        fread(pivot, COMB_SIZE, 1, pivots_fp);

        while (fread(comb, COMB_SIZE, 1, combs_fp))
        {
            if (comb_sum_cmp(comb, pivot) >= 0)
            {
                fprintf(stderr, "  Error!!!\n");
                break;
            }

            ct = ccd_check_for_coll(ccd, comb, &other_comb);
            if (ct == coll_type_ident)
            {
                printf("  Collision between identical elements.\n");
            }
            else if (ct == coll_type_diff)
            {
                printf("  Collision between different elements!!!\n  ");
                for (j = 0; j < COMB_SIZE; j++)
                    printf("%02x", comb[j]);
                printf("\n  ");
                for (j = 0; j < COMB_SIZE; j++)
                    printf("%02x", other_comb[j]);
                printf("\n");
            }
        }

        fclose(combs_fp);
        printf(" DONE in %fs.\n", timer_elapsed());
    }

    comb_free();
    ccd_free(ccd);
    fclose(pivots_fp);

    return 0;
}
