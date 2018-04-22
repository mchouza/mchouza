gcc -c a.c -o a.o
yasm b.s -f macho64 -m amd64 -o b.o
gcc -o exe a.o b.o
