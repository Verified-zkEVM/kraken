.set heap_start, 0x20000000
.set heap_end,   0x78000000
.set fill_byte,  0xa5

.macro expect_allocation address, next
    cmp $\address, %rax
    jne fail
    cmpq $\next, x1_next(%rip)
    jne fail
.endm

.macro expect_bytes address, length, value
    mov $\address, %edi
    mov $\length, %ecx
    mov $\value, %al
    repe scasb
    jne fail
.endm

.text
.globl _start
_start:
    mov (%rsp), %r12
    and $-16, %rsp
    cld
    mov $9, %eax
    mov $heap_start, %edi
    mov $(heap_end - heap_start), %esi
    mov $3, %edx
    mov $0x100022, %r10d
    mov $-1, %r8
    xor %r9d, %r9d
    syscall
    cmp $heap_start, %rax
    jne fail
    cmpq $heap_start, x1_next(%rip)
    jne fail

    cmp $2, %r12
    je outside_contract
    cmp $1, %r12
    jne fail

    mov $heap_start, %edi
    mov $64, %ecx
    mov $fill_byte, %al
    rep stosb
    movq $(heap_start + 1), x1_next(%rip)
    mov $16, %edi
    mov $8, %esi
    call x1_alloc
    expect_allocation (heap_start + 8), (heap_start + 24)
    expect_bytes heap_start, 64, fill_byte

    mov $16, %edi
    xor %esi, %esi
    call x1_alloc_zeroed
    expect_allocation (heap_start + 24), (heap_start + 40)
    expect_bytes heap_start, 24, fill_byte
    expect_bytes (heap_start + 24), 16, 0
    expect_bytes (heap_start + 40), 24, fill_byte

    mov $7, %edi
    call x1_alloc_zeroed
    expect_allocation (heap_start + 40), (heap_start + 47)
    expect_bytes heap_start, 24, fill_byte
    expect_bytes (heap_start + 24), 23, 0
    expect_bytes (heap_start + 47), 17, fill_byte

    mov $(heap_start + 49), %edi
    mov $0x2345fe, %esi
    mov $3, %edx
    call memset
    cmp $(heap_start + 49), %rax
    jne fail
    expect_bytes (heap_start + 47), 2, fill_byte
    expect_bytes (heap_start + 49), 3, 0xfe
    expect_bytes (heap_start + 52), 12, fill_byte
    xor %edi, %edi
    mov $0x1234, %esi
    xor %edx, %edx
    call memset
    test %rax, %rax
    jne fail

    mov $(heap_end - 16), %edi
    mov $16, %ecx
    mov $fill_byte, %al
    rep stosb
    movq $(heap_end - 8), x1_next(%rip)
    mov $8, %edi
    mov $8, %esi
    call x1_alloc
    expect_allocation (heap_end - 8), heap_end
    expect_bytes (heap_end - 16), 16, fill_byte

    movq $(heap_end - 8), x1_next(%rip)
    mov $8, %edi
    call x1_alloc_zeroed
    expect_allocation (heap_end - 8), heap_end
    expect_bytes (heap_end - 16), 8, fill_byte
    expect_bytes (heap_end - 8), 8, 0

    mov $8, %edi
    mov $8, %esi
    call x1_alloc
    expect_allocation 0, heap_end
    mov $8, %edi
    call x1_alloc_zeroed
    expect_allocation 0, heap_end

    movq $(heap_end - 7), x1_next(%rip)
    mov $1, %edi
    mov $8, %esi
    call x1_alloc
    expect_allocation 0, (heap_end - 7)
    mov $1, %edi
    call x1_alloc_zeroed
    expect_allocation 0, (heap_end - 7)
    expect_bytes (heap_end - 16), 8, fill_byte
    expect_bytes (heap_end - 8), 8, 0

    xor %edi, %edi
    jmp exit
outside_contract:
    mov $1, %edi
    movabs $0x100000000, %rsi
    call x1_alloc
fail:
    mov $1, %edi
exit:
    mov $60, %eax
    syscall
.section .note.GNU-stack,"",@progbits
