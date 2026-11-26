.text
.globl probe_bsr
.type probe_bsr, @function
probe_bsr:
    mov %rcx, %r8
    pushfq
    pop %rax
    and $~0xcd5, %rax
    or %rdx, %rax
    push %rax
    popfq
    mov %rdi, %rdx
    mov %rsi, %rcx
    pushfq
    pop %r9
    .byte 0x48, 0x0f, 0xbd, 0xca
    pushfq
    pop %rax
    cld
    mov %rcx, 0(%r8)
    mov %rdx, 8(%r8)
    mov %r9, 16(%r8)
    mov %rax, 24(%r8)
    ret
.size probe_bsr, . - probe_bsr
.section .note.GNU-stack,"",@progbits
