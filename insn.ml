type operand =
    Hard_reg of int
  | Immediate of int32
  | Address of int32
  | Stack of int

and cc_bits = C | V | N | Z
	    | C_zero | C_one | C_from_shift

and condition = Eq | Ne | Cs | Cc | Mi | Pl | Vs | Vc
	      | Hi | Ls | Ge | Lt | Gt | Le

type opcode =
    Ldr of access_info
  | Str of access_info
  | Ldrb of access_info
  | Strb of access_info
  | And
  | Eor
  | Sub
  | Rsb
  | Add
  | Adc
  | Sbc
  | Rsc
  | Tst
  | Teq
  | Cmp
  | Cmn
  | Orr
  | Mov
  | Bic
  | Mvn
  | Shifted of opcode * shift_opcode
  | Conditional of condition * opcode
  | BAD

and shift_opcode =
    Lsl
  | Lsr
  | Asr
  | Ror
  | Rrx

and addr_mode =
    Base_plus_imm
  | Base_plus_reg
  | Base_minus_reg
  | Base_plus_shifted_reg of shift_opcode
  | Base_minus_shifted_reg of shift_opcode

and access_info =
  {
    addr_mode : addr_mode;
    writeback : bool;
    pre_modify : bool
  }

type insn =
  {
    opcode : opcode;
    write_operands : operand array;
    read_operands : operand array;
    write_flags : cc_bits list;
    (* READ_FLAGS does *not* count flags required by insn
       conditionalisation!  *)
    read_flags : cc_bits list;
    clobber_flags : cc_bits list
  }
