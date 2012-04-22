(* Convert decoded INSN format into IR code type.  *)

open Insn

module IL = Ir.IrCS
module IT = Ir.IrCT
module C = Ir.Ir

let pseudo_num = ref 0

let flags_match a b =
  (List.sort compare a) = (List.sort compare b)

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
    IL.snoc ilist (C.Set (dst, C.Trinary (opcode, op1, op2,
		     C.Reg (IT.Status Irtypes.Carry))))
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
    let ilist = IL.snoc ilist (C.Store (access, addr, src)) in
    if ainf.writeback then
      let w_base = convert_operand insn.write_operands.(0) in
      IL.snoc ilist (C.Set (w_base, addr))
    else
      ilist
  end else begin
    assert ainf.writeback;
    let w_base = convert_operand insn.write_operands.(0) in
    let ilist = IL.snoc ilist (C.Store (access, base, src)) in
    IL.snoc ilist (C.Set (w_base, addr))
  end

let convert_bx insn ilist =
  let dest = insn.read_operands.(0) in
  match dest with
    Hard_reg r ->
      let ctrl = C.Control (C.Jump_ext (IT.Branch_exchange, IT.Reg_addr r)) in
      IL.snoc ilist ctrl
  | _ -> failwith "unexpected bx operand"

let convert_condition cond =
  let code =
    match cond with
      Ne -> Irtypes.Status_ne
    | Eq -> Irtypes.Status_eq
    | Lt -> Irtypes.Status_lt
    | Le -> Irtypes.Status_le
    | Gt -> Irtypes.Status_gt
    | Ge -> Irtypes.Status_ge
    | Mi -> Irtypes.Status_ltu
    | Pl -> Irtypes.Status_geu
    | Hi -> Irtypes.Status_gtu
    | Ls -> Irtypes.Status_leu
    | Cc -> Irtypes.Status_cc
    | Cs -> Irtypes.Status_cs
    | Vc -> Irtypes.Status_vc
    | Vs -> Irtypes.Status_vs in
  C.Unary (code, C.Reg (IT.Status Irtypes.CondFlags))

let convert_cond_bx cond addr insn ilist =
  let dest = insn.read_operands.(0) in
  match dest with
    Hard_reg r ->
      let falseblock = Int32.add addr 4l in
      let ctrl = C.Control (C.Branch (convert_condition cond, falseblock,
			    falseblock)) in
      IL.snoc ilist ctrl
  | _ -> failwith "unexpected bx operand"

let find_symbol symbols addr =
  try
    let symbol = Symbols.find_symbol_by_addr symbols addr in
    IT.Symbol symbol
  with Not_found ->
    IT.Absolute addr

let convert_bl symbols addr insn ilist =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let no_arg = C.Nullary Irtypes.Nop in
      let ret_addr = Int32.add addr 4l in
      let call_addr = Int32.add addr i in
      let sym_or_addr = find_symbol symbols call_addr in
      let ctrl = C.Control (C.Call_ext (IT.Unknown_abi, sym_or_addr,
					no_arg, ret_addr, no_arg)) in
      IL.snoc ilist ctrl
  | _ -> failwith "unexpected bx operand"

let convert_cmp insn ilist =
  if insn.read_flags = [] && flags_match insn.write_flags [C;V;N;Z] then begin
    let op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    IL.snoc ilist (C.Set (C.Reg (IT.Status Irtypes.CondFlags),
		    C.Binary (Irtypes.Cmp, op1, op2)))
  end else
    IL.snoc ilist (C.Nullary (Irtypes.Untranslated))

let convert_cbranch cond addr insn ilist =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let trueblock = Int32.add addr i
      and falseblock = Int32.add addr 4l in
      let branch = C.Control (C.Branch (convert_condition cond, trueblock,
					falseblock)) in
      IL.snoc ilist branch
  | _ -> failwith "unexpected b<cond> operand"

let convert_branch addr insn ilist =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let branch = C.Control (C.Jump (Int32.add addr i)) in
      IL.snoc ilist branch
  | _ -> failwith "unexpected b operand"

exception Unsupported_opcode of Insn.opcode

let rec convert_insn symbols addr insn ilist =
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
  | Cmp -> convert_cmp insn ilist
  | Ldr ainf -> convert_load ainf insn Irtypes.Word ilist
  | Ldrb ainf -> convert_load ainf insn Irtypes.U8 ilist
  | Str ainf -> convert_store ainf insn Irtypes.Word ilist
  | Strb ainf -> convert_store ainf insn Irtypes.U8 ilist
  | Bx -> convert_bx insn ilist
  | Bl -> convert_bl symbols addr insn ilist
  | B -> convert_branch addr insn ilist
  | Conditional (cond, B) -> convert_cbranch cond addr insn ilist
  | Conditional (cond, Bx) -> convert_cond_bx cond addr insn ilist
  | x -> raise (Unsupported_opcode x)

let convert_block symbols addr insn_list =
  let code_deque, last_offset = Deque.fold_left
    (fun (acc, offset) insn ->
      let ilist' = convert_insn symbols (Int32.add addr offset) insn acc in
      ilist', Int32.add offset 4l)
    (IL.empty, 0l)
    insn_list in
  if not (IL.is_empty code_deque) then
    match IL.noced code_deque with
      prev, C.Control _ -> code_deque
    | _ ->
      let fallthru = C.Control (C.Jump (Int32.add addr last_offset)) in
      IL.snoc code_deque fallthru
  else
    code_deque
  
