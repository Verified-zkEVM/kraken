# Undefined flags: cf, pf, af, zf, sf, of

movabsq $0x1111111100000001, %rax
movabsq $0x2222222200000001, %rdx
movabsq $0x3333333300000002, %rsi
divl %esi
movq %rax, %r8
movq %rdx, %r9
movq %rsi, %r10

movabsq $0x1111111100000003, %rax
movabsq $0x2222222200000001, %rdx
divl %eax
movq %rax, %r11
movq %rdx, %r12

movabsq $0x4000000000000000, %rax
movq $0, %rdx
movq $94, %rsi
divq %rsi
