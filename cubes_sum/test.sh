gcc -std=c99 -O3 cubes_sum.naive.c -o cubes_sum.naive-c
nasm -f elf64 cubes_sum.naive-asm.s
ld cubes_sum.naive-asm.o -o cubes_sum.naive-asm
echo 'Naive C version'
time ./cubes_sum.naive-c >output-naive-c
echo 'Naive ASM version'
time ./cubes_sum.naive-asm >output-naive-asm
sort output-naive-c -o output-naive-c
sort output-naive-asm -o output-naive-asm
diff output-naive-c output-naive-asm
rm cubes_sum.naive-c cubes_sum.naive-asm.o cubes_sum.naive-asm output-*