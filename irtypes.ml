type ir_nulop =
    Nop
  | Untranslated
  | Caller_saved
  | Arg_in
  | Special
  | Incoming_sp
  | Declaration of Ctype.ctype

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
  | Address_of
  | Aggr_member of Ctype.ctype * aggr_member_id
  | Uxtb
  | Sxtb
  | Uxth
  | Sxth

(* Code will look like:

   Set (dst, Load (Word, Unop (Aggr_member (Aggr_leaf "x"), SSAReg foo)))
   
   Store (Word, Unop (Aggr_member (Aggr_leaf "y"), SSAReg foo), src)
*)

and aggr_member_id =
    Aggr_leaf of string
  | Aggr_sub of string * aggr_member_id

type ir_binop =
    Add
  | Sub
  | And
  | Eor
  | Or
  | Mul
  | Cmp
  | Cmn
  | Tst
  | Lsl
  | Lsr
  | Asr
  | Ror
  | Rrx

type ir_triop =
    Adc
  | Sbc
  | Mla

type ir_extop =
    Fnargs

type ir_mem =
    U8
  | S8
  | U16
  | S16
  | Word
  | Dword

type ir_statusbits =
    Carry      (* Just the carry flag.  *)
  | CondFlags  (* All the condition flags: C, V, N & Z.  *)
  | NZFlags    (* Just the N & Z flags.  *)

type ir_blockref =
    BlockAddr of int32
  | BlockNum of int
  | Virtual_entry
  | Virtual_exit
