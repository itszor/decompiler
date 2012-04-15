open Insn

let string_of_operand = function
    Hard_reg r -> "r" ^ string_of_int r
  | Immediate i -> Int32.to_string i
  | _ -> "<<unsupported>>"

let emit_load' fh insn ainf fn_name addr_op =
  if ainf.pre_modify then begin
    Printf.fprintf fh "%s = %s (%s %s %s);\n"
      (string_of_operand insn.write_operands.(0)) fn_name
      (string_of_operand insn.read_operands.(0)) addr_op
      (string_of_operand insn.read_operands.(1));
    if ainf.writeback then
      Printf.fprintf fh "%s = %s %s %s;\n"
	(string_of_operand insn.write_operands.(1))
	(string_of_operand insn.read_operands.(0)) addr_op
	(string_of_operand insn.read_operands.(1))
  end else begin
    Printf.fprintf fh "%s = %s (%s);\n"
      (string_of_operand insn.write_operands.(0)) fn_name
      (string_of_operand insn.read_operands.(0));
    assert ainf.writeback;
    Printf.fprintf fh "%s = %s %s %s;\n"
      (string_of_operand insn.write_operands.(1))
      (string_of_operand insn.read_operands.(0)) addr_op
      (string_of_operand insn.read_operands.(1))
  end

let emit_load fh insn ainf fn_name =
  match ainf.addr_mode with
    Base_plus_imm
  | Base_plus_reg -> emit_load' fh insn ainf fn_name "+"
  | Base_minus_reg -> emit_load' fh insn ainf fn_name "-"

let emit_store' fh insn ainf fn_name addr_op =
  if ainf.pre_modify then begin
    Printf.fprintf fh "%s (%s, %s %s %s);\n"
      fn_name (string_of_operand insn.read_operands.(0))
      (string_of_operand insn.read_operands.(1)) addr_op
      (string_of_operand insn.read_operands.(2));
    if ainf.writeback then
      Printf.fprintf fh "%s = %s %s %s;\n"
	(string_of_operand insn.write_operands.(0))
	(string_of_operand insn.read_operands.(1)) addr_op
	(string_of_operand insn.read_operands.(2))
  end else begin
    Printf.fprintf fh "%s (%s, %s);\n"
      fn_name (string_of_operand insn.read_operands.(0))
      (string_of_operand insn.read_operands.(1));
    assert ainf.writeback;
    Printf.fprintf fh "%s = %s %s %s;\n"
      (string_of_operand insn.write_operands.(0))
      (string_of_operand insn.read_operands.(1)) addr_op
      (string_of_operand insn.read_operands.(2))
  end

let emit_store fh insn ainf fn_name =
  match ainf.addr_mode with
    Base_plus_imm
  | Base_plus_reg -> emit_store' fh insn ainf fn_name "+"
  | Base_minus_reg -> emit_store' fh insn ainf fn_name "-"

let emit_binop fh opname insn =
  if insn.read_flags = [] && insn.write_flags = [] then
    Printf.fprintf fh "%s = %s %s %s;\n"
      (string_of_operand insn.write_operands.(0))
      (string_of_operand insn.read_operands.(0))
      opname
      (string_of_operand insn.read_operands.(1))
  else
    Printf.fprintf fh "<<unsupported>>\n"

let emit_insn fh insn =
  match insn.opcode with
    Ldr ainf -> emit_load fh insn ainf "ldr"
  | Str ainf -> emit_store fh insn ainf "str"
  | Ldrb ainf -> emit_load fh insn ainf "ldrb"
  | Strb ainf -> emit_store fh insn ainf "strb"
  | Add -> emit_binop fh "+" insn
  | And -> emit_binop fh "&" insn
  | Eor -> emit_binop fh "^" insn
  | Orr -> emit_binop fh "|" insn
  | Sub -> emit_binop fh "-" insn
  | Mul -> emit_binop fh "*" insn
  | _ -> Printf.fprintf fh "abort ();\n"
