SECTIONS {
  .x1_alloc : { KEEP(*(.text._RNvCsGIExRX8pES_7___rustc12___rust_alloc)) } :code
  .x1_alloc_zeroed : { KEEP(*(.text._RNvCsGIExRX8pES_7___rustc19___rust_alloc_zeroed)) } :code
  x1_alloc = ADDR(.x1_alloc);
  x1_alloc_zeroed = ADDR(.x1_alloc_zeroed);
} INSERT BEFORE .text;

SECTIONS {
  .rela.text : { *(.rela.text) } :ro
  .x1_next ALIGN(0x1000) : { KEEP(*(.data._ZN7x1entry7runtime4NEXT17h6b462ab609bd49c9E.0)) } :data
  x1_next = ADDR(.x1_next);
  ASSERT(SIZEOF(.rela.text) == 0, "Unexpected text relocations")
} INSERT BEFORE .data;
