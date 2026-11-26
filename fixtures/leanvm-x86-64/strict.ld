ENTRY(_start)
PHDRS
{
  code PT_LOAD FILEHDR PHDRS FLAGS(5);
  ro PT_LOAD FLAGS(4);
  data PT_LOAD FLAGS(6);
  stack PT_GNU_STACK FLAGS(6);
}
SECTIONS
{
  . = 0x400000 + SIZEOF_HEADERS;
  .fixture : {
    KEEP(*(.text._ZN8verifier11multilinear13stack_offsets17h895bb5299dc153eeE))
  } :code
  fixture = ADDR(.fixture);
  .text : { *(.text .text.*) } :code
  .iplt : { *(.iplt) } :code
  . = ALIGN(0x1000);
  .rodata : { *(.rodata .rodata.*) } :ro
  .data.rel.ro : { *(.data.rel.ro .data.rel.ro.*) } :ro
  .got : { *(.got) *(.got.plt) } :ro
  .igot.plt : { *(.igot.plt) } :ro
  .rela.got : { *(.rela.got) } :ro
  .rela.iplt : { *(.rela.iplt) } :ro
  . = ALIGN(0x1000);
  .data : { *(.data .data.*) } :data
  .bss : { *(.bss .bss.*) *(COMMON) } :data
  .symtab 0 : { *(.symtab) } :NONE
  .strtab 0 : { *(.strtab) } :NONE
  .shstrtab 0 : { *(.shstrtab) } :NONE
  ASSERT(SIZEOF(.iplt) == 0, "Unexpected IFUNC PLT")
  ASSERT(SIZEOF(.igot.plt) == 0, "Unexpected IFUNC GOT")
  ASSERT(SIZEOF(.rela.got) == 0, "Unexpected GOT relocations")
  ASSERT(SIZEOF(.rela.iplt) == 0, "Unexpected IFUNC relocations")
  /DISCARD/ : { *(.debug_* .comment .note.GNU-stack) }
}
