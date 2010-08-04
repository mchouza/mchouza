#include "fb_bucket.h"
#include "basic.h"
#include <stdio.h>
#include <string.h>

#define FBBH(bucket) ((fb_bucket_head_t*)bucket)

typedef struct
{
    size_t elem_size;
    size_t max_num_elems;
    size_t num_elems;
    char* fname;
    byte data[1];
} fb_bucket_head_t;

fb_bucket_t* fbb_create(size_t elem_size, size_t max_num_elems, 
                        const char* fname)
{
    size_t bucket_size;
    size_t fname_len;
    FILE* fp;
    fb_bucket_t* bucket;

    bucket_size = sizeof(fb_bucket_head_t) - 1 + elem_size * max_num_elems;
    fname_len = strlen(fname);

    /* files are not kept open to avoid the maximum opened streams limit */
    fp = fopen(fname, "a+b");
    if (!fp)
        return NULL;
    fclose(fp);

    bucket = malloc(bucket_size);
    FBBH(bucket)->elem_size = elem_size;
    FBBH(bucket)->max_num_elems = max_num_elems;
    FBBH(bucket)->num_elems = 0;
    FBBH(bucket)->fname = malloc(fname_len + 1);
    strcpy(FBBH(bucket)->fname, fname);

    return bucket;
}

fb_bucket_t* fbb_add_elem(fb_bucket_t* bucket, const void* elem)
{
    size_t byte_index;
    
    if (FBBH(bucket)->num_elems == FBBH(bucket)->max_num_elems)
        if (!fbb_flush(bucket))
            return NULL;

    byte_index = FBBH(bucket)->num_elems * FBBH(bucket)->elem_size;

    memcpy(&FBBH(bucket)->data[byte_index], elem, FBBH(bucket)->elem_size);

    FBBH(bucket)->num_elems++;

    return bucket;
}

fb_bucket_t* fbb_flush(fb_bucket_t* bucket)
{
    FILE* fp;

    fp = fopen(FBBH(bucket)->fname, "ab");
    if (!fp)
        return NULL;

    if (fwrite(FBBH(bucket)->data, FBBH(bucket)->elem_size, 
               FBBH(bucket)->num_elems, fp) != FBBH(bucket)->num_elems )
    {
        fclose(fp);
        return NULL;
    }

    FBBH(bucket)->num_elems = 0;
    
    fclose(fp);

    return bucket;
}

void fbb_destroy(fb_bucket_t* bucket)
{
    if (!bucket)
        return;
    fbb_flush(bucket);
    free(FBBH(bucket)->fname);
    free(bucket);
}
