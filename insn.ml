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
    Ldr
  | Str
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

type insn =
  {
    opcode : opcode;
    write_operands : operand array;
    read_operands : operand array;
    write_flags : cc_bits list;
    read_flags : cc_bits list;
    clobber_flags : cc_bits list
  }
