(* Convert decoded INSN format into IR code type.  *)

open Insn

module IL = Ir.IrCS
module IT = Ir.IrCT
module C = Ir.Ir

let pseudo_num = ref 0

let create_pseudo () =
  let tmp = IT.Temp !pseudo_num in
  incr pseudo_num;
  tmp

let convert_operand op =
  match op with
    Hard_reg r -> C.Reg (IT.Hard_reg r)
  | Immediate i -> C.Immed i
  | _ -> failwith "boo"

let convert_mov insn ilist =
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0) in
    IL.snoc ilist (C.Set (dst, op1))
  end else
    IL.snoc ilist (C.Nullary (Irtypes.Untranslated))

let convert_binop opcode insn ilist =
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    IL.snoc ilist (C.Set (dst, C.Binary (opcode, op1, op2)))
  end else
    IL.snoc ilist (C.Nullary (Irtypes.Untranslated))

let convert_rsb insn ilist =
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    IL.snoc ilist (C.Set (dst, C.Binary (Irtypes.Sub, op2, op1)))
  end else
    IL.snoc ilist (C.Nullary (Irtypes.Untranslated))

let convert_carry_in_op opcode insn ilist =
  if insn.write_flags = [] && insn.read_flags = [C] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    IL.snoc ilist (C.Set (dst, C.Trinary (opcode, op1, op2, C.Reg (IT.Carry))))
  end else
    IL.snoc ilist (C.Nullary (Irtypes.Untranslated))

let convert_address ainf insn base index =
  match ainf.addr_mode with
    Base_plus_imm
  | Base_plus_reg -> C.Binary (Irtypes.Add, base, index)
  | Base_minus_reg -> C.Binary (Irtypes.Sub, base, index)

let convert_load ainf insn access ilist =
  let base = convert_operand insn.read_operands.(0)
  and index = convert_operand insn.read_operands.(1) in
  let addr = convert_address ainf insn base index
  and dst = convert_operand insn.write_operands.(0) in
  if ainf.pre_modify then begin
    let ilist = IL.snoc ilist (C.Set (dst, C.Load (access, addr))) in
    if ainf.writeback then
      let w_base = convert_operand insn.write_operands.(1) in
      IL.snoc ilist (C.Set (w_base, addr))
    else
      ilist
  end else begin
    assert ainf.writeback;
    let w_base = convert_operand insn.write_operands.(1) in
    let ilist = IL.snoc ilist (C.Set (dst, C.Load (access, base))) in
    IL.snoc ilist (C.Set (w_base, addr))
  end

let convert_store ainf insn access ilist =
  let base = convert_operand insn.read_operands.(1)
  and index = convert_operand insn.read_operands.(2) in
  let addr = convert_address ainf insn base index
  and src = convert_operand insn.read_operands.(0) in
  if ainf.pre_modify then begin
    let ilist = IL.snoc ilist (C.Store (access, src, addr)) in
    if ainf.writeback then
      let w_base = convert_operand insn.write_operands.(0) in
      IL.snoc ilist (C.Set (w_base, addr))
    else
      ilist
  end else begin
    assert ainf.writeback;
    let w_base = convert_operand insn.write_operands.(0) in
    let ilist = IL.snoc ilist (C.Store (access, src, base)) in
    IL.snoc ilist (C.Set (w_base, addr))
  end

let convert_bx insn ilist =
  let dest = insn.read_operands.(0) in
  match dest with
    Hard_reg r ->
      let ctrl = C.Control (C.Jump_ext (IT.Branch_exchange, IT.Reg_addr r)) in
      IL.snoc ilist ctrl
  | _ -> failwith "unexpected bx operand"

let convert_bl insn ilist =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      (*let ctrl = C.Control (C.Call_ext (IT.Unknown_abi, IT.Absolute i)) in*)
      IL.snoc ilist (C.Nullary Irtypes.Untranslated)
  | _ -> failwith "unexpected bx operand"

exception Unsupported_opcode of Insn.opcode

let convert_insn insn ilist =
  match insn.opcode with
    Mov -> convert_mov insn ilist
  | Add -> convert_binop Irtypes.Add insn ilist
  | Sub -> convert_binop Irtypes.Sub insn ilist
  | And -> convert_binop Irtypes.And insn ilist
  | Eor -> convert_binop Irtypes.Eor insn ilist
  | Orr -> convert_binop Irtypes.Or insn ilist
  | Mul -> convert_binop Irtypes.Mul insn ilist
  | Rsb -> convert_rsb insn ilist
  | Adc -> convert_carry_in_op Irtypes.Adc insn ilist
  | Sbc -> convert_carry_in_op Irtypes.Sbc insn ilist
  | Ldr ainf -> convert_load ainf insn Irtypes.Word ilist
  | Ldrb ainf -> convert_load ainf insn Irtypes.U8 ilist
  | Str ainf -> convert_store ainf insn Irtypes.Word ilist
  | Strb ainf -> convert_store ainf insn Irtypes.U8 ilist
  | Bx -> convert_bx insn ilist
  | Bl -> convert_bl insn ilist
  | x -> raise (Unsupported_opcode x)

let convert_block insn_list =
  Deque.fold_right
    (fun insn acc -> convert_insn insn acc)
    insn_list
    IL.empty
