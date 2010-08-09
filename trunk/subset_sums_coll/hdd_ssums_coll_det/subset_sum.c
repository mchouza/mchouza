#include "bignum.h"
#include "comb_gen.h"
#include "comb_sum.h"
#include "timer.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NUM_COMBS_ITER 10000000
#define COMB_SIZE 10
#define NUM_ITERS 2000
#define MAX_FPATH 256
#define FPATH_FMT "g:\\subset_sums_data\\%04d.bin"
#define PIVOTS_FPATH "g:\\subset_sums_data\\pivots.bin"
#define NUM_FILES 1000

int comb_sum_cmp(const void* comb1, const void* comb2)
{
    bignum_t op1, op2;
    comb_fast_sum(&op1, (const byte*)comb1);
    comb_fast_sum(&op2, (const byte*)comb2);
    return bignum_cmp(&op1, &op2);
}

void fill_comb_buffer(byte* comb_buffer)
{
    int i;
    for (i = 0; i < NUM_COMBS_ITER; i++)
        gen_random_comb(&comb_buffer[i * 10], 70, 35);
}

void get_pivots(byte* pivots, const byte* sorted_combs)
{
    int i;
    for (i = 1; i < NUM_FILES; i++)
        memcpy(&pivots[(i - 1) * COMB_SIZE], 
               &sorted_combs[i * (NUM_COMBS_ITER / NUM_FILES) * COMB_SIZE],
               COMB_SIZE);
    memset(&pivots[(NUM_FILES - 1) * COMB_SIZE], 0xff, COMB_SIZE);
}

void save_pivots(const byte* pivots)
{
    FILE* fp;
    fp = fopen(PIVOTS_FPATH, "wb");
    fwrite(pivots, COMB_SIZE, NUM_FILES, fp);
    fclose(fp);
}

FILE* open_comb_file(size_t i, const char* mode)
{
    char fpath[MAX_FPATH];
    sprintf(fpath, FPATH_FMT, i);
    return fopen(fpath, mode);
}

void create_output_files(void)
{
    int i;
    for (i = 0; i < NUM_FILES; i++)
        fclose(open_comb_file(i, "wb"));
}

void save_comb_buffer(const byte* comb_buffer, const byte* pivots)
{
    FILE* fp;
    int i, j;
    
    i = 0;
    fp = open_comb_file(i, "ab");

    for (j = 0; j < NUM_COMBS_ITER; j++)
    {
        while (comb_sum_cmp(&comb_buffer[j * 10], &pivots[i * 10]) >= 0)
        {
            fclose(fp);
            fp = open_comb_file(++i, "ab");
        }
        fwrite(&comb_buffer[j * 10], COMB_SIZE, 1, fp);
    }

    fclose(fp);
}

int main(void)
{
    byte* buffer;
    byte* pivots;
    size_t i;

    comb_init();  
    buffer = malloc(NUM_COMBS_ITER * COMB_SIZE);
    pivots = malloc(NUM_FILES * COMB_SIZE);

    for (i = 0; i < NUM_ITERS; i++)
    {
        printf("\nIteration %d of %d.\n\n", i + 1, NUM_ITERS);

        printf("Filling combinations buffer...");
        timer_reset();
        fill_comb_buffer(buffer);
        printf(" DONE in %fs.\n", timer_elapsed());

        printf("Sorting combinations buffer...");
        timer_reset();
        qsort(buffer, NUM_COMBS_ITER, COMB_SIZE, comb_sum_cmp);
        printf(" DONE in %fs.\n", timer_elapsed());

        if (i == 0)
        {
            printf("Creating output files...");
            create_output_files();
            printf(" DONE.\n");

            printf("Getting and saving pivots...");
            get_pivots(pivots, buffer);
            save_pivots(pivots);
            printf(" DONE.\n");
        }

        printf("Saving sorted combinations buffer...");
        timer_reset();
        save_comb_buffer(buffer, pivots);
        printf(" DONE in %fs.\n", timer_elapsed());
    }

    free(buffer);
    free(pivots);
    comb_free();

    return 0;
}
