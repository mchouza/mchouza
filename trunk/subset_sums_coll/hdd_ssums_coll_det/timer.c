#include <windows.h>
#include "timer.h"

static LARGE_INTEGER timer_start;

void timer_reset(void)
{
    QueryPerformanceCounter(&timer_start);
}

double timer_elapsed(void)
{
    LARGE_INTEGER timer_now;
    LARGE_INTEGER timer_freq;
    double elapsed_time;
    QueryPerformanceCounter(&timer_now);
    elapsed_time = (double)(timer_now.HighPart - timer_start.HighPart);
    elapsed_time *= 4294967296.0;
    elapsed_time += (double)(timer_now.LowPart - timer_start.LowPart);
    QueryPerformanceFrequency(&timer_freq);
    elapsed_time /= timer_freq.LowPart;
    return elapsed_time;
}