type operand =
    Hard_reg of int
  | Immediate of int32
  | CC of cc_bits list
  | Address of int32

and cc_bits = C | V | N | Z

and condition = Eq | Ne | Cs | Cc | Mi | Pl | Vs | Vc
	      | Hi | Ls | Ge | Lt | Gt | Le

let cc_all = [C; V; N; Z]

type opcode =
    Ldr
  | Str
  | And
  | BAD

type insn =
  {
    opcode : opcode;
    write_operands : operand array;
    read_operands : operand array;
    condition : condition option
  }
