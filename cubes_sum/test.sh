set -e
rm -f cubes_sum.*-c cubes_sum.*-asm.o cubes_sum.*-asm output-*
echo -n 'Processor: '
grep '^model name' /proc/cpuinfo | sed 's/[^:]*:\s*//' | uniq
gcc -std=c99 -O3 cubes_sum.naive.c -o cubes_sum.naive-c
gcc -std=c99 -O3 cubes_sum.bounds.c -lm -o cubes_sum.bounds-c
gcc -std=c99 -O3 -msse4.1 cubes_sum.intrinsics.c -o cubes_sum.intrinsics-c
gcc -std=c99 -O3 -mavx2 cubes_sum.intrinsics-avx2.c -o cubes_sum.intrinsics-avx2-c
nasm -f elf64 cubes_sum.naive-asm.s
ld cubes_sum.naive-asm.o -o cubes_sum.naive-asm
set +e
echo -ne '\nNaive C version'; time ./cubes_sum.naive-c >output-naive-c
echo -ne '\nBounds-using C version'; time ./cubes_sum.bounds-c >output-bounds-c
echo -ne '\nSSE4.1 Intrinsics C version'; time ./cubes_sum.intrinsics-c >output-intrinsics-c
echo -ne '\nAVX2 Intrinsics C version'; time ./cubes_sum.intrinsics-avx2-c >output-intrinsics-avx2-c
echo -ne '\nNaive ASM version'; time ./cubes_sum.naive-asm >output-naive-asm
sort output-naive-c -o output-naive-c
sort output-bounds-c -o output-bounds-c
sort output-intrinsics-c -o output-intrinsics-c
sort output-intrinsics-avx2-c -o output-intrinsics-avx2-c
sort output-naive-asm -o output-naive-asm
set -e
diff output-naive-c output-bounds-c
diff output-naive-c output-intrinsics-c
diff output-naive-c output-intrinsics-avx2-c
diff output-naive-c output-naive-asm