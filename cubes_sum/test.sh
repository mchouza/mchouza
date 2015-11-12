set -e
gcc -std=c99 -O3 cubes_sum.naive.c -o cubes_sum.naive-c
gcc -std=c99 -O3 -msse4.1 cubes_sum.intrinsics.c -o cubes_sum.intrinsics-c
nasm -f elf64 cubes_sum.naive-asm.s
ld cubes_sum.naive-asm.o -o cubes_sum.naive-asm
echo 'Naive C version'
time ./cubes_sum.naive-c >output-naive-c
echo 'Intrinsics C version'
time ./cubes_sum.intrinsics-c >output-intrinsics-c
echo 'Naive ASM version'
time ./cubes_sum.naive-asm >output-naive-asm
sort output-naive-c -o output-naive-c
sort output-intrinsics-c -o output-intrinsics-c
sort output-naive-asm -o output-naive-asm
diff output-naive-c output-intrinsics-c
diff output-naive-c output-naive-asm
rm cubes_sum.*-c cubes_sum.*-asm.o cubes_sum.*-asm output-*