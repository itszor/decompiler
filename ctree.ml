(* Tree representation of program elements.  Uses AST from FrontC.  *)

open Cabs

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

let convert_basetype ctyp =
  let rec convert = function
    Ctype.C_void -> VOID
  | Ctype.C_longlong -> INT (LONG_LONG, SIGNED)
  | Ctype.C_int -> INT (NO_SIZE, NO_SIGN)
  | Ctype.C_signed Ctype.C_int -> INT (NO_SIZE, SIGNED)
  | Ctype.C_unsigned Ctype.C_int -> INT (NO_SIZE, UNSIGNED)
  | Ctype.C_short -> INT (SHORT, NO_SIGN)
  | Ctype.C_signed Ctype.C_short -> INT (SHORT, SIGNED)
  | Ctype.C_unsigned Ctype.C_short -> INT (SHORT, UNSIGNED)
  | Ctype.C_char -> CHAR NO_SIGN
  | Ctype.C_unsigned Ctype.C_char -> CHAR UNSIGNED
  | Ctype.C_signed Ctype.C_char -> CHAR SIGNED
  | Ctype.C_float -> FLOAT false
  | Ctype.C_double -> DOUBLE false
  | Ctype.C_pointer targ -> PTR (convert targ)
  | Ctype.C_const targ -> CONST (convert targ)
  | Ctype.C_volatile targ -> VOLATILE (convert targ)
  | Ctype.C_struct (nm, aglist) -> convert_struct nm aglist
  | Ctype.C_union (nm, aglist) -> convert_union nm aglist
  | Ctype.C_enum -> ENUM ("", [])
  | Ctype.C_typedef nm -> (* ?? *) NAMED_TYPE nm
  | Ctype.C_typetag nm -> (* ?? *) NAMED_TYPE nm
  | Ctype.C_array (bound, typ) ->
      ARRAY (convert typ, CONSTANT (CONST_INT (string_of_int bound)))
  | Ctype.C_funtype _ -> failwith "convert_basetype/funtype"
  | _ -> failwith "convert_basetype"
  and convert_struct nm aglist =
    STRUCT (nm, List.map convert_namegroup aglist)
  and convert_union nm aglist =
    UNION (nm, List.map convert_namegroup aglist)
  and convert_namegroup aggr_mem =
    let base_type = convert aggr_mem.Ctype.typ
    and storage = (* ?? *) NO_STORAGE in
    let name = aggr_mem.Ctype.name, base_type, [], NOTHING in
    base_type, storage, [name] in
  convert ctyp

let rec basetype_for_type = function
    Ctype.C_pointer x -> basetype_for_type x
  | Ctype.C_array (_, x) -> basetype_for_type x
  | Ctype.C_const (Ctype.C_pointer x) -> basetype_for_type x
  | Ctype.C_volatile (Ctype.C_pointer x) -> basetype_for_type x
  | x -> x

(* Make a Cabs.definition list for a Hashtbl (from ssa names to) variables,
   VARS.  *)

let convert_vardecls vars =
  Hashtbl.fold
    (fun _ vtyp decllist ->
      if vtyp.Vartypes.vt_needs_prototype then
	let basetype = basetype_for_type vtyp.Vartypes.vt_type in
	let name = vtyp.Vartypes.vt_name,
		     convert_basetype vtyp.Vartypes.vt_type, [], NOTHING in
	let decl = DECDEF (convert_basetype basetype, NO_STORAGE, [name]) in
	decl :: decllist
      else
        decllist)
    vars
    []

let seq_append seq comp =
  match seq with
    NOP -> comp
  | cur -> SEQUENCE (cur, comp)

let operand_type vars op =
  match op with
    C.Immed _ -> Ctype.C_int
  | C.SSAReg (r, rn) ->
      begin try
        let vtyp = Hashtbl.find vars (Vartypes.T_ssareg (r, rn)) in
	vtyp.Vartypes.vt_type
      with Not_found ->
        Log.printf 1 "No type for SSA variable %s\n"
	  (Typedb.string_of_ssa_reg r rn);
        Ctype.C_void
      end
  | C.Reg r ->
      begin try
        let vtyp = Hashtbl.find vars (Vartypes.T_reg r) in
	vtyp.Vartypes.vt_type
      with Not_found ->
        Log.printf 1 "No type for variable %s\n"
	  (CT.string_of_reg r);
	Ctype.C_void
      end
  | C.Entity (CT.Section nm) ->
      Log.printf 1 "Warning, unresolved section ref for %s\n" nm;
      Ctype.C_pointer (Ctype.C_void)
  | _ ->
      Log.printf 1 "Warning, unsupported operand %s\n" (C.string_of_code op);
      Ctype.C_void

let typesize_scale typesize op =
  match op with
    C.Immed imm ->
      let i32typesize = Int32.of_int typesize in
      if Int32.rem imm i32typesize = 0l then
        C.Immed (Int32.div imm i32typesize)
      else begin
        Log.printf 1 "typesize: %d, op %s\n" typesize (C.string_of_code op);
        C.Immed imm
      end
  | C.SSAReg regid ->
      C.Binary (Irtypes.Div, op, C.Immed (Int32.of_int typesize))
  | _ ->
      Log.printf 1 "typesize_scale: unsupported: %s\n" (C.string_of_code op);
      failwith "unsupported"

let rec convert_expr ct_for_cu vars op =
  match op with
    C.Binary (binop, op1, op2) ->
      convert_binop ct_for_cu vars binop op1 op2
  | C.Unary (unop, op1) ->
      convert_unop ct_for_cu vars unop op1
  | C.Immed imm ->
      Cabs.CONSTANT (Cabs.CONST_INT (Int32.to_string imm))
  | C.SSAReg (r, rn) ->
      begin try
        let vtyp = Hashtbl.find vars (Vartypes.T_ssareg (r, rn)) in
	Cabs.VARIABLE vtyp.Vartypes.vt_name
      with Not_found ->
	Cabs.VARIABLE (Printf.sprintf
	  "(unknown var %s)" (Typedb.string_of_ssa_reg r rn))
      end
  | C.Entity (CT.Stack_var sv) ->
      Cabs.VARIABLE sv
  | C.Load (accsz, addr) ->
      let conv_addr = convert_expr ct_for_cu vars addr in
      Cabs.UNARY (Cabs.MEMOF, conv_addr)
  | C.Entity (CT.Section name) ->
      Cabs.VARIABLE ("SECTION_" ^ name)
  | C.Entity (CT.String_constant str) ->
      Cabs.CONSTANT (Cabs.CONST_STRING str)
  | C.Entity (CT.Symbol_addr (nm, elfsym)) ->
      Cabs.UNARY (Cabs.ADDROF, Cabs.VARIABLE nm)
  | C.Call_ext (_, callee, args) ->
      convert_extcall ct_for_cu vars callee args
  | C.Nullary Irtypes.Nop ->
      Cabs.NOTHING
  | _ ->
      Log.printf 1 "convert_expr: unsupported: %s\n" (C.string_of_code op);
      Cabs.NOTHING

and convert_binop ct_for_cu vars binop op1 op2 =
  let ot1 = operand_type vars op1
  and ot2 = operand_type vars op2 in
  let tk1 = Ctype.type_kind ct_for_cu ot1
  and tk2 = Ctype.type_kind ct_for_cu ot2 in
  let op1' = convert_expr ct_for_cu vars op1
  and op2' = convert_expr ct_for_cu vars op2 in
  match binop, tk1, tk2 with
    Irtypes.Add, (`signed|`unsigned), (`signed|`unsigned) ->
      Cabs.BINARY (Cabs.ADD, op1', op2')
  | Irtypes.Add, `ptr, (`signed|`unsigned) ->
      let ptt = Ctype.pointed_to_type ct_for_cu ot1 in
      let typesize = Ctype.type_size ct_for_cu ptt in
      let mod_op2 = convert_expr ct_for_cu vars (typesize_scale typesize op2) in
      Cabs.BINARY (Cabs.ADD, op1', mod_op2)
  | Irtypes.Add, (`signed|`unsigned), `ptr ->
      Cabs.BINARY (Cabs.ADD, op1', op2')
  | Irtypes.Sub, (`signed|`unsigned), (`signed|`unsigned) ->
      Cabs.BINARY (Cabs.SUB, op1', op2')
  | Irtypes.Sub, `ptr, (`signed|`unsigned) ->
      let ptt = Ctype.pointed_to_type ct_for_cu ot1 in
      let typesize = Ctype.type_size ct_for_cu ptt in
      let mod_op2 = convert_expr ct_for_cu vars (typesize_scale typesize op2) in
      Cabs.BINARY (Cabs.SUB, op1', mod_op2)
  | Irtypes.Sub, `ptr, `ptr ->
      Cabs.BINARY (Cabs.SUB, op1', op2')
  | Irtypes.Lsl, (`signed|`unsigned), (`signed|`unsigned) ->
      Cabs.BINARY (Cabs.SHL, op1', op2')
  | Irtypes.Lsr, (`signed|`unsigned), (`signed|`unsigned) ->
      let op1'' = Cabs.CAST (Cabs.INT (Cabs.NO_SIZE, Cabs.UNSIGNED), op1') in
      Cabs.BINARY (Cabs.SHR, op1'', op2')
  | Irtypes.Asr, (`signed|`unsigned), (`signed|`unsigned) ->
      let op1'' = Cabs.CAST (Cabs.INT (Cabs.NO_SIZE, Cabs.SIGNED), op1') in
      Cabs.BINARY (Cabs.SHR, op1'', op2')
  | _ ->
      Log.printf 1 "unsupported binop: %s (%s, %s)\n"
	(CT.string_of_binop binop) (Ctype.string_of_ctype ot1)
	(Ctype.string_of_ctype ot2);
      Cabs.NOTHING

and convert_unop ct_for_cu vars unop op1 =
  let ot1 = operand_type vars op1 in
  let tk1 = Ctype.type_kind ct_for_cu ot1 in
  let op1' = convert_expr ct_for_cu vars op1 in
  match unop, tk1 with
    Irtypes.Aggr_member ag, _ ->
      Cabs.MEMBEROFPTR (op1', ag)
  | _ ->
      Log.printf 1 "unsupported unop: %s (%s)\n"
	(CT.string_of_unop unop) (Ctype.string_of_ctype ot1);
      Cabs.NOTHING

and convert_move ct_for_cu vars dst conv_rhs acc =
  let dst' = convert_expr ct_for_cu vars dst in
  let move_insn = Cabs.COMPUTATION
		    (Cabs.BINARY (Cabs.ASSIGN, dst', conv_rhs)) in
  seq_append acc move_insn
      
and convert_args ct_for_cu vars args =
  match args with
    C.Nary (Irtypes.Fnargs, arglist) ->
      List.map (fun arg -> convert_expr ct_for_cu vars arg) arglist
  | C.Nullary Irtypes.Nop -> []
  | _ -> failwith "unexpected"

and convert_extcall ct_for_cu vars callee args =
  match callee with
    CT.Symbol (name, _)
  | CT.Finf_sym (name, _, _) ->
      Cabs.CALL (Cabs.VARIABLE name, convert_args ct_for_cu vars args)
  | CT.Absolute _ -> failwith "unimplemented"

and convert_return ct_for_cu vars retcode acc =
  seq_append acc (Cabs.RETURN (convert_expr ct_for_cu vars retcode))

and convert_branch ct_for_cu vars cond trueblk falseblk fallthru acc =
  let cond' = convert_expr ct_for_cu vars cond in
  let ifstmt =
    match fallthru with
      Some fallthru when fallthru.Block.id = trueblk ->
	Cabs.IF (cond', Cabs.BLOCK ([], Cabs.NOP),
		 Cabs.GOTO (Ir.IrBS.string_of_blockref falseblk))
    | Some fallthru when fallthru.Block.id = falseblk ->
	Cabs.IF (cond', Cabs.GOTO (Ir.IrBS.string_of_blockref trueblk),
		 Cabs.NOP)
    | _ ->
	Cabs.IF (cond', Cabs.GOTO (Ir.IrBS.string_of_blockref trueblk),
		 Cabs.GOTO (Ir.IrBS.string_of_blockref falseblk)) in
  seq_append acc ifstmt

and convert_jump ct_for_cu vars dst fallthru acc =
  match fallthru with
    Some fallthru when fallthru.Block.id = dst ->
      acc
  | _ ->
      Cabs.GOTO (Ir.IrBS.string_of_blockref dst)

and convert_compjump ct_for_cu vars swval dests fallthru acc =
  let caseseq, _ =
    List.fold_left
      (fun (acc, num) which ->
        let thiscase =
	  Cabs.CASE (Cabs.CONSTANT (Cabs.CONST_INT (string_of_int num)),
		     Cabs.GOTO (Ir.IrBS.string_of_blockref which)) in
	seq_append acc thiscase, succ num)
      (Cabs.NOP, 0)
      dests in
  (* Redundant...  *)
  (* let caseseq =
    match fallthru with
      Some fallthru ->
        seq_append caseseq (Cabs.DEFAULT (Cabs.GOTO 
	  (Ir.IrBS.string_of_blockref fallthru.Block.id)))
    | _ -> caseseq in *)
  Cabs.SWITCH (convert_expr ct_for_cu vars swval, Cabs.BLOCK ([], caseseq))

and convert_control ct_for_cu vars ctl fallthru acc =
  match ctl with
    C.Return retcode ->
      convert_return ct_for_cu vars retcode acc
  | C.Branch (cond, trueblk, falseblk) ->
      convert_branch ct_for_cu vars cond trueblk falseblk fallthru acc
  | C.Jump dst ->
      convert_jump ct_for_cu vars dst fallthru acc
  | C.CompJump (swval, dests) ->
      convert_compjump ct_for_cu vars swval dests fallthru acc
  | C.CompJump_ext (abi, dest) ->
      Cabs.NOP
  | _ ->
      failwith (Printf.sprintf "unsupported control: %s"
        (C.string_of_control ctl))

(* Convert a block of code.  *)

let convert_block blk fallthru ct_for_cu vars seq =
  let block_seq = CS.fold_left
    (fun acc insn ->
      match insn with
        C.Set (dst, src) ->
          convert_move ct_for_cu vars dst (convert_expr ct_for_cu vars src) acc
      | C.Store (accsz, addr, valu) ->
	  let conv_addr = convert_expr ct_for_cu vars addr in
	  let store =
	    Cabs.BINARY (Cabs.ASSIGN, Cabs.UNARY (Cabs.MEMOF, conv_addr),
			 convert_expr ct_for_cu vars valu) in
	  seq_append acc (Cabs.COMPUTATION store)
      | C.Control ctl ->
          convert_control ct_for_cu vars ctl fallthru acc
      | C.Entity (CT.Insn_address _) -> acc
      | C.Call_ext (_, dst, args) ->
          seq_append acc (Cabs.COMPUTATION (convert_extcall ct_for_cu vars dst
					    args))
      | _ ->
          Log.printf 1 "unsupported: %s\n" (C.string_of_code insn);
	  acc)
    NOP
    blk.Block.code in
  seq_append seq (LABEL (Ir.IrBS.string_of_blockref blk.Block.id, block_seq))

let convert_blocks blk_arr ct_for_cu vars =
  let _, seq =
    Array.fold_left
      (fun (idx, seq) blk ->
        let fallthru =
	  if idx < Array.length blk_arr - 1 then
	    Some blk_arr.(idx + 1)
	  else
	    None in
	match blk.Block.id with
          Irtypes.Virtual_entry
	| Irtypes.Virtual_exit -> succ idx, seq
	| _ ->
	    let seq' = convert_block blk fallthru ct_for_cu vars seq in
	    succ idx, seq')
      (0, NOP)
      blk_arr in
  seq

let convert_function fname ftype vars ct_for_cu blk_arr =
  let return_type = convert_basetype ftype.Function.return in
  let args = ref [] in
  let nargs = Array.length ftype.Function.args in
  for i = nargs - 1 downto 0 do
    let base_type = convert_basetype ftype.Function.args.(i) in
    let arg_name = ftype.Function.arg_names.(i), base_type, [], NOTHING in
    let arg_sname = base_type, NO_STORAGE, arg_name in
    args := arg_sname :: !args
  done;
  let proto = return_type, !args, false in
  let return_name = fname, PROTO proto, [], NOTHING in
  let return_singlename = return_type, NO_STORAGE, return_name in
  let vardecls = convert_vardecls vars in
  let fn_body = convert_blocks blk_arr ct_for_cu vars in
  let body = vardecls, fn_body in
  FUNDEF (return_singlename, body)
  
let convert_typedef typename dtype =
  let basetype = convert_basetype dtype in
  let name = typename, basetype, [], NOTHING in
  let namegroup = basetype, NO_STORAGE, [name] in 
  TYPEDEF (namegroup, [])
