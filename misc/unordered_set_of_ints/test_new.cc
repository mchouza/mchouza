#include <cstdint>
#include <cstdio>
#include <cstdlib>

int main(int argc, char *argv[])
{
    size_t s = atoi(argv[1]);
    uint32_t *p = new uint32_t[s];
    for (size_t i = 0; i < s; i++)
        p[i] = i;
    int ret = system("ps aux | egrep \"(USER|$PPID)\\s\"");
    delete[] p;
    return ret;
}
