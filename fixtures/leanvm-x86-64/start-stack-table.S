.set guard_base,   0x10000000
.set page_size,    0x1000
.set stack_base,   guard_base + page_size
.set stack_budget, 0x4000
.ifndef stack_size
.set stack_size,   0x10000
.endif
.set stack_top,    (stack_base + stack_size) & -16
.set sentinel_rbx, 0x1122334455667788
.set sentinel_rbp, 0x2233445566778899
.set sentinel_r12, 0x33445566778899aa
.set sentinel_r13, 0x445566778899aabb
.set sentinel_r14, 0x5566778899aabbcc
.set sentinel_r15, 0x66778899aabbccdd

.text
.globl _start
_start:
    cmpq $2, (%rsp)
    jne fail
    mov 16(%rsp), %rax
    movzbl (%rax), %ebx
    sub $48, %ebx
    cmp $10, %ebx
    ja fail
    and $-16, %rsp
    mov $9, %eax
    mov $0x20000000, %edi
    mov $0x58000000, %esi
    mov $3, %edx
    mov $0x100022, %r10d
    mov $-1, %r8
    xor %r9d, %r9d
    syscall
    cmp $0x20000000, %rax
    jne fail
    mov $9, %eax
    mov $guard_base, %edi
    mov $(stack_size + page_size), %esi
    xor %edx, %edx
    mov $0x100022, %r10d
    mov $-1, %r8
    xor %r9d, %r9d
    syscall
    cmp $guard_base, %rax
    jne fail

    mov $10, %eax
    mov $stack_base, %edi
    mov $stack_size, %esi
    mov $3, %edx
    syscall
    test %rax, %rax
    jne fail

.ifdef inspect_guard
    mov $39, %eax
    syscall
    mov %eax, %edi
    mov $19, %esi
    mov $62, %eax
    syscall
    test %rax, %rax
    jne fail
.endif

    mov $stack_top, %r13d
    lea -8(%r13), %rcx
    cmp $stack_base, %rcx
    jb reject_stack
    sub $stack_base, %rcx
    cmp $stack_budget, %rcx
    jb reject_stack

    lea cases(%rip), %r12
    shl $5, %rbx
    add %rbx, %r12

    mov 8(%r12), %rdx
    cmp $stack_table_len, %rdx
    jae reject_range
    lea stack_table(%rip), %rax
    cmpq $stack_budget, (%rax,%rdx,8)
    ja reject_input

    lea result(%rip), %rdi
    mov 0(%r12), %rsi
    mov %r12, selected_case(%rip)
    mov %r13, %rsp
    movabs $sentinel_rbx, %rbx
    movabs $sentinel_rbp, %rbp
    movabs $sentinel_r12, %r12
    movabs $sentinel_r13, %r13
    movabs $sentinel_r14, %r14
    movabs $sentinel_r15, %r15
    call fixture

.ifdef break_check
.if break_check == 0
    mov %ebx, %ebx
.elseif break_check == 1
    mov %ebp, %ebp
.elseif break_check == 2
    mov %r12d, %r12d
.elseif break_check == 3
    mov %r13d, %r13d
.elseif break_check == 4
    mov %r14d, %r14d
.elseif break_check == 5
    mov %r15d, %r15d
.elseif break_check == 6
    sub $8, %rsp
.elseif break_check == 7
    incq result(%rip)
.else
    .error "break_check must be in 0 through 7"
.endif
.endif

    cmp $stack_top, %rsp
    jne reject_abi
    movabs $sentinel_rbx, %rax
    cmp %rax, %rbx
    jne reject_abi
    movabs $sentinel_rbp, %rax
    cmp %rax, %rbp
    jne reject_abi
    movabs $sentinel_r12, %rax
    cmp %rax, %r12
    jne reject_abi
    movabs $sentinel_r13, %rax
    cmp %rax, %r13
    jne reject_abi
    movabs $sentinel_r14, %rax
    cmp %rax, %r14
    jne reject_abi
    movabs $sentinel_r15, %rax
    cmp %rax, %r15
    jne reject_abi

    lea result(%rip), %rdi
    mov selected_case(%rip), %r12
    mov 8(%r12), %rcx
    cmp %rcx, 0(%rdi)
    jne reject_abi
    cmp %rcx, 16(%rdi)
    jne fail
    mov 24(%r12), %rax
    cmp %rax, 24(%rdi)
    jne fail
    mov 8(%rdi), %rsi
    mov 16(%r12), %rdi
    repe cmpsq
    jne fail
    xor %edi, %edi
    jmp exit
reject_stack:
    mov $42, %edi
    jmp exit
reject_input:
    mov $43, %edi
    jmp exit
reject_range:
    mov $44, %edi
    jmp exit
reject_abi:
    mov $1, %edi
    jmp exit
fail:
    mov $2, %edi
exit:
    mov $60, %eax
    syscall
.section .rodata
.balign 8
cases:
    .quad input0, 0, expected0, 0
    .quad input1, 1, expected1, 0
    .quad input2, 1, expected2, 63
    .quad input3, 4, expected3, 4
    .quad input4, 96, expected4, 10
    .quad input5, 97, expected5, 7
    .quad input5, 98, expected5, 7
    .quad input5, 0x200000000000000, expected5, 0
    .quad input94, 94, expected94, 13
    .quad input54, 54, expected54, 12
    .quad input45, 45, expected45, 12
input94:
    .quad 0, 7, 5, 2, 2, 7, 4, 6, 4, 6, 6, 6
    .quad 8, 5, 3, 0, 0, 6, 3, 5, 3, 4, 4, 4
    .quad 7, 5, 1, 0, 7, 5, 0, 4, 0, 2, 4, 2
    .quad 6, 1, 1, 5, 7, 4, 8, 3, 8, 2, 0, 2
    .quad 5, 3, 1, 3, 3, 3, 0, 7, 5, 7, 2, 2
    .quad 0, 6, 8, 5, 1, 7, 4, 1, 8, 5, 5, 0
    .quad 3, 1, 2, 1, 3, 1, 1, 5, 5, 7, 0, 3
    .quad 7, 6, 6, 6, 8, 5, 4, 8, 0, 3
expected94:
    .quad 4472, 1792, 3712, 4416, 4420, 1920, 4160, 3072, 4176, 3136, 3200, 3264
    .quad 0, 3744, 4320, 4473, 4474, 3328, 4328, 3776, 4336, 4192, 4208, 4224
    .quad 2048, 3808, 4452, 4475, 2176, 3840, 4476, 4240, 4477, 4424, 4256, 4428
    .quad 3392, 4454, 4456, 3872, 2304, 4272, 256, 4344, 512, 4432, 4478, 4436
    .quad 3904, 4352, 4458, 4360, 4368, 4376, 4479, 2432, 3936, 2560, 4440, 4444
    .quad 4480, 3456, 768, 3968, 4460, 2688, 4288, 4462, 1024, 4000, 4032, 4481
    .quad 4384, 4464, 4448, 4466, 4392, 4468, 4470, 4064, 4096, 2816, 4482, 4400
    .quad 2944, 3520, 3584, 3648, 1280, 4128, 4304, 1536, 4483, 4408
input54:
    .quad 0, 7, 5, 2, 2, 7, 4, 6, 4, 6, 6, 6
    .quad 8, 5, 3, 0, 0, 6, 3, 5, 3, 4, 4, 4
    .quad 7, 5, 1, 0, 7, 5, 0, 4, 0, 2, 4, 2
    .quad 6, 1, 1, 5, 7, 4, 8, 3, 8, 2, 0, 2
    .quad 5, 3, 1, 3, 3, 3
expected54:
    .quad 2240, 768, 1792, 2208, 2212, 896, 2016, 1408, 2032, 1472, 1536, 1600
    .quad 0, 1824, 2144, 2241, 2242, 1664, 2152, 1856, 2160, 2048, 2064, 2080
    .quad 1024, 1888, 2232, 2243, 1152, 1920, 2244, 2096, 2245, 2216, 2112, 2220
    .quad 1728, 2234, 2236, 1952, 1280, 2128, 256, 2168, 512, 2224, 2246, 2228
    .quad 1984, 2176, 2238, 2184, 2192, 2200
input45:
    .quad 0, 7, 5, 2, 2, 7, 4, 6, 4, 6, 6, 6
    .quad 8, 5, 3, 0, 0, 6, 3, 5, 3, 4, 4, 4
    .quad 7, 5, 1, 0, 7, 5, 0, 4, 0, 2, 4, 2
    .quad 6, 1, 1, 5, 7, 4, 8, 3, 8
expected45:
    .quad 2166, 768, 1792, 2144, 2148, 896, 1984, 1408, 2000, 1472, 1536, 1600
    .quad 0, 1824, 2112, 2167, 2168, 1664, 2120, 1856, 2128, 2016, 2032, 2048
    .quad 1024, 1888, 2160, 2169, 1152, 1920, 2170, 2064, 2171, 2152, 2080, 2156
    .quad 1728, 2162, 2164, 1952, 1280, 2096, 256, 2136, 512
input0:
    .quad 0
expected0:
    .quad 0
input1:
    .quad 0
expected1:
    .quad 0
input2:
    .quad 63
expected2:
    .quad 0
input3:
    .quad 2, 1, 2, 0
expected3:
    .quad 0, 8, 4, 10
input4:
    .quad 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4
expected4:
    .quad 640, 512, 0, 641, 516, 16, 642, 520, 32, 643, 524, 48, 644, 528, 64, 645, 532, 80, 646, 536, 96, 647, 540, 112, 648, 544, 128, 649, 548, 144, 650, 552, 160, 651, 556, 176, 652, 560, 192, 653, 564, 208, 654, 568, 224, 655, 572, 240, 656, 576, 256, 657, 580, 272, 658, 584, 288, 659, 588, 304, 660, 592, 320, 661, 596, 336, 662, 600, 352, 663, 604, 368, 664, 608, 384, 665, 612, 400, 666, 616, 416, 667, 620, 432, 668, 624, 448, 669, 628, 464, 670, 632, 480, 671, 636, 496
input5:
    .zero 784
expected5:
    .quad 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96
.balign 8
stack_table:
    .incbin "stack-table.bin"
stack_table_end:
.set stack_table_len, (stack_table_end - stack_table) / 8
.bss
.balign 8
result: .skip 32
selected_case: .skip 8
.section .note.GNU-stack,"",@progbits
