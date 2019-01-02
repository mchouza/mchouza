#include <fcntl.h>
#include <memory.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#define BUFFER_LEN (256 << 20)
#define MIN(a, b) ((a) < (b) ? (a) : (b))

void memrep1(uint8_t *buffer, size_t buffer_len, uint8_t from, uint8_t to)
{
    for (size_t i = 0; i < buffer_len; i++)
        if (buffer[i] == from)
            buffer[i] = to;
}

void memrep2(uint8_t *dst_buffer, const uint8_t *src_buffer, 
             size_t buffer_len, uint8_t from, uint8_t to)
{
    for (size_t i = 0; i < buffer_len; i++)
        dst_buffer[i] = src_buffer[i] == from ? to : src_buffer[i];
}

uint8_t sum(const uint8_t *buffer, size_t buffer_len)
{
    uint8_t ret = 0;
    for (size_t i = 0; i < buffer_len; i++)
        ret += buffer[i];
    return ret;
}

void fill_random(uint8_t *buffer, size_t buffer_len)
{
    int fd = open("/dev/urandom", O_RDONLY); 
    for (size_t i = 0; i < buffer_len; i += (1 << 16))
        read(fd, &buffer[i], MIN((1 << 16), buffer_len - i));
    close(fd);
}

int main(void)
{
    uint8_t *src_buffer = malloc(BUFFER_LEN);
    uint8_t *dst_buffer = malloc(BUFFER_LEN);
    fill_random(src_buffer, BUFFER_LEN);

    clock_t start = clock();
    uint8_t src_buffer_sum = sum(src_buffer, BUFFER_LEN);
    clock_t end = clock();
    printf("Buffer sum: %u\n", src_buffer_sum);
    printf("Buffer sum - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);

    start = clock();
    memcpy(dst_buffer, src_buffer, BUFFER_LEN);
    end = clock();
    printf("Buffer copy - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);

    start = clock();
    uint8_t dst_buffer_sum = sum(dst_buffer, BUFFER_LEN);
    end = clock();
    printf("Buffer sum 2: %u\n", dst_buffer_sum);
    printf("Buffer sum 2 - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);
    
    start = clock();
    memrep1(dst_buffer, BUFFER_LEN, 42, 43);
    end = clock();
    printf("memrep1 - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);

    start = clock();
    dst_buffer_sum = sum(dst_buffer, BUFFER_LEN);
    end = clock();
    printf("Buffer sum 3: %u\n", dst_buffer_sum);
    printf("Buffer sum 3 - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);
    
    start = clock();
    memrep2(dst_buffer, src_buffer, BUFFER_LEN, 45, 46);
    end = clock();
    printf("memrep2 - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);

    start = clock();
    dst_buffer_sum = sum(dst_buffer, BUFFER_LEN);
    end = clock();
    printf("Buffer sum 4: %u\n", dst_buffer_sum);
    printf("Buffer sum 4 - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);
    
    start = clock();
    memrep1(dst_buffer, BUFFER_LEN, 42, 43);
    end = clock();
    printf("memrep1 (2nd) - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);

    start = clock();
    dst_buffer_sum = sum(dst_buffer, BUFFER_LEN);
    end = clock();
    printf("Buffer sum 5: %u\n", dst_buffer_sum);
    printf("Buffer sum 5 - elapsed time: %.2f ms\n", 
           1e3 * (double)(end - start) / CLOCKS_PER_SEC);

    free(src_buffer);
    free(dst_buffer);

    return 0;
}
