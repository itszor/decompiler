type ir_nulop =
    Nop
  | Untranslated
  | Caller_saved
  | Arg_in
  | Special

type ir_unop =
    Not
  | Status_eq
  | Status_ne
  | Status_lt
  | Status_le
  | Status_gt
  | Status_ge
  | Status_ltu
  | Status_leu
  | Status_gtu
  | Status_geu
  | Status_cc
  | Status_cs
  | Status_vc
  | Status_vs

type ir_binop =
    Add
  | Sub
  | And
  | Eor
  | Or
  | Mul
  | Cmp

type ir_triop =
    Adc
  | Sbc

type ir_mem =
    U8
  | S8
  | U16
  | S16
  | Word

type ir_statusbits =
    Carry      (* Just the carry flag.  *)
  | CondFlags  (* All the condition flags: C, V, N & Z.  *)
  | NZFlags    (* Just the N & Z flags.  *)

type ir_blockref = int32
