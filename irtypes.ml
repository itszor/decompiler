type ir_nulop =
    Nop

type ir_unop =
    Not

type ir_binop =
    Add
  | Sub
  | And
  | Eor
  | Or
  | Mul

type ir_triop =
    Adc
  | Sbc

type ir_mem =
    U8
  | S8
  | U16
  | S16
  | Word
