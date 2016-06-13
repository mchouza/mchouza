#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_set>

int main(int argc, char *argv[])
{
    size_t s = atoi(argv[1]);
    std::unordered_set<uint32_t> p;
    for (size_t i = 0; i < s; i++)
        p.insert(i);
    return system("ps aux | egrep \"(USER|$PPID)\\s\"");
}
