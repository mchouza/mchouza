;; Cubes sum problem in x86-64

section .data
nl:   db 10

section .bss
digits: resb 3

section .text

global _start

_start:

    mov rax, 999
loop_a:

    ; rdx = 10^6 * rax
    mov rdx, 1000000
    imul rdx, rax

    ; rsi = rax * rax * rax
    mov rsi, rax
    imul rsi, rax
    imul rsi, rax

    mov rbx, 999
loop_b:

    ; r10 = 10^6 * rax + 10^3 * rbx
    mov r10, 1000
    imul r10, rbx
    add r10, rdx

    ; r12 = rax * rax * rax + rbx * rbx * rbx
    mov r12, rbx
    imul r12, rbx
    imul r12, rbx
    add r12, rsi

    mov rcx, 999
loop_c:

    ; r13 = 10^6 * rax + 10^3 * rbx + rcx
    mov r13, r10
    add r13, rcx

    ; r14 = rax * rax * rax + rbx * rbx * rbx + rcx * rcx * rcx
    mov r14, rcx
    imul r14, rcx
    imul r14, rcx
    add r14, r12

    ; skips printing if r13 != r14
    cmp r13, r14
    jne skip_print

    ; preserves rax, rcx, rsi, rdx
    mov r8, rax
    mov r9, rcx
    mov r13, rsi
    mov r14, rdx

    ; prints the value
    mov rax, r8
    call print_three_digits
    mov rax, rbx
    call print_three_digits
    mov rax, r9
    call print_three_digits

    ; prints a newline
    mov rax, 1
    mov rdi, 1
    mov rsi, nl
    mov rdx, 1
    syscall

    ; restores rax, rcx, rsi, rdx
    mov rax, r8
    mov rcx, r9
    mov rsi, r13
    mov rdx, r14

skip_print:
    
    ; loop for c
    sub rcx, 1
    jae loop_c

    ; loop for b 
    sub rbx, 1
    jae loop_b

    ; loop for a 
    sub rax, 1
    jae loop_a

    ; exits with success
    mov rax, 60
    mov rdi, 0
    syscall

; prints the contents of rax as a three digit number
print_three_digits:

    ; calculates the three digits
    mov rdx, 0
    mov rcx, 100
    div rcx
    add rax, 48
    mov [digits], rax
    mov rax, rdx
    mov rdx, 0
    mov rcx, 10
    div rcx
    add rax, 48
    mov [digits+1], rax
    add rdx, 48
    mov [digits+2], rdx

    ; prints those three digits
    mov rax, 1
    mov rdi, 1
    mov rsi, digits
    mov rdx, 3
    syscall

    ; returns
    ret