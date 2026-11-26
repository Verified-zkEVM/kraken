.text
.globl probe_div32
.type probe_div32, @function
probe_div32:
    movq %rdi, %rax
    xchgq %rsi, %rdx
.globl probe_div32_opcode
probe_div32_opcode:
    .byte 0xf7, 0xf6
    movq %rax, 0(%rcx)
    movq %rdx, 8(%rcx)
    movq %rsi, 16(%rcx)
    ret
.size probe_div32, . - probe_div32

.globl probe_div64
.type probe_div64, @function
probe_div64:
    movq %rdi, %rax
    xchgq %rsi, %rdx
.globl probe_div64_opcode
probe_div64_opcode:
    .byte 0x48, 0xf7, 0xf6
    movq %rax, 0(%rcx)
    movq %rdx, 8(%rcx)
    movq %rsi, 16(%rcx)
    ret
.size probe_div64, . - probe_div64
.section .note.GNU-stack,"",@progbits
