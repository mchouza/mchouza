#ifndef FB_BUCKET_H
#define FB_BUCKET_H

#include <stdlib.h>

/* file-backed bucket */
typedef void fb_bucket_t;

fb_bucket_t* fbb_create(size_t elem_size, size_t max_num_elems, 
                        const char* fname);
fb_bucket_t* fbb_add_elem(fb_bucket_t* bucket, const void* elem);
fb_bucket_t* fbb_flush(fb_bucket_t* bucket);
void fbb_destroy(fb_bucket_t* bucket);

#endif
