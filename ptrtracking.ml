open Defs

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

(* We can sometimes tell the names and proper types of registers too -- that's
   not handled at present, and probably won't be handled here anyway.  *)

let fb_relative_var_loc loc =
  match loc with
    Dwarfreader.Loc_expr (`DW_OP_fbreg offs) -> offs
  (*| Dwarfreader.Loc_list _ -> failwith "unimplemented"*)
  | _ -> raise Not_found

let known_var vars sp_offset =
  let fv, ofs =
    List.fold_left
      (fun ((found_var, offset) as prev) var ->
	match var.Function.var_location with
          None -> prev
	| Some loc ->
            try
	      let var_offset = fb_relative_var_loc loc in
	      if sp_offset >= var_offset
		 && sp_offset < (var_offset + var.Function.var_size) then begin
		Log.printf 3 "sp offset:%d var_offset:%d var_size:%d\n"
		  sp_offset var_offset var.Function.var_size;
		Some var, sp_offset - var_offset
	      end else
		prev
	    with Not_found -> prev)
      (None, 0)
      vars in
  match fv with
    Some f -> f, ofs
  | None -> raise Not_found

module IrPhiPlacement = Phi.PhiPlacement (Ir.IrCT) (Ir.IrCS) (Ir.IrBS)

let try_rewrite_access var_reg var_type aggr_access rewrite_as =
  match rewrite_as with
    `load (_, dst) -> (* FIXME: Verify access size!  *)
      C.Set (dst, C.Unary (Irtypes.Aggr_member (var_type, aggr_access),
			   var_reg))
  | `store (_, src) -> (* FIXME: Verify access size!  *)
      C.Set (C.Unary (Irtypes.Aggr_member (var_type, aggr_access),
		      var_reg), src)
  | `ssa_reg ->
      C.Unary (Irtypes.Address_of,
	       C.Unary (Irtypes.Aggr_member (var_type, aggr_access), var_reg))

let try_rewrite_var vars base offset stack_vars vartype_hash insn rewrite_as
		    ctypes_for_cu =
  match base, vartype_hash with
    C.Nullary Irtypes.Incoming_sp, _ ->
      begin try
	let kvar, var_ofs = known_var vars offset in
	Log.printf 3 "Offset %d looks like variable %s (+%d)\n"
	  offset kvar.Function.var_name var_ofs;
	let sv = CT.Stack_var kvar.Function.var_name in
	stack_vars := IrPhiPlacement.R.add sv !stack_vars;
	let aggr_access, _ =
	  Insn_to_ir.resolve_aggregate_access kvar.Function.var_type var_ofs
					      ctypes_for_cu in
	(*let blk = {
	  Irtypes.ctype = kvar.Function.var_type;
	  block_size = kvar.Function.var_size;
	  access_size = Irtypes.Word
	} in*)
      try_rewrite_access (C.Reg sv) kvar.Function.var_type aggr_access
			 rewrite_as
      with Not_found | Insn_to_ir.Non_aggregate ->
	Log.printf 3 "Not found/non-aggregate at offset %d\n" offset;
	insn
      end
  | C.SSAReg regid, Some vh ->
      begin try
        let vti = Hashtbl.find vh (Vartypes.T_ssareg regid) in
	let aggr_access, _ =
	  Insn_to_ir.resolve_aggregate_access vti.Vartypes.vt_type offset
					      ctypes_for_cu in
	try_rewrite_access base vti.Vartypes.vt_type aggr_access rewrite_as
      with Not_found | Insn_to_ir.Non_aggregate ->
        Log.printf 3 "Type missing or non-aggregate for %s\n"
	  (Typedb.string_of_ssa_reg (fst regid) (snd regid));
	insn
      end
  | C.Reg reg, Some vh ->
      begin try
        let vti = Hashtbl.find vh (Vartypes.T_reg reg) in
	Log.printf 3 "Type for %s is %s\n" (C.string_of_code base)
	  (Ctype.string_of_ctype vti.Vartypes.vt_type);
	let aggr_access, _ =
	  Insn_to_ir.resolve_aggregate_access vti.Vartypes.vt_type offset
					      ctypes_for_cu in
	try_rewrite_access base vti.Vartypes.vt_type aggr_access rewrite_as
      with Not_found | Insn_to_ir.Non_aggregate ->
        Log.printf 3 "Type missing or non-aggregate for %s\n"
	  (CT.string_of_reg reg);
	insn
      end
  | _, _ -> insn

exception Untrackable

(* Given a use of an SSA variable USE (a pointer, or suspected to be one),
   return a list of (def, offset) pairs. Raise Untrackable if it cannot be
   done.  *)

let track_pointer defs use =
  let rec track use offset =
    try
      let dinf = Hashtbl.find defs use in
      match dinf.src with
	C.SSAReg (d, dn) -> (dinf.src, offset) :: track (d, dn) offset
      | C.Binary (Irtypes.Add, (C.SSAReg (d, dn) as reg), C.Immed imm) ->
          let offset' = Int32.add offset imm in
	  (reg, offset') :: track (d, dn) offset'
      | C.Binary (Irtypes.Sub, (C.SSAReg (d, dn) as reg), C.Immed imm) ->
          let offset' = Int32.sub offset imm in
	  (reg, offset') :: track (d, dn) offset'
      | C.Nullary Irtypes.Caller_saved
      | C.Nullary Irtypes.Special
      | C.Nullary Irtypes.Incoming_sp
      (*| C.Nullary (Irtypes.Arg_in _)*)
      | C.Entity CT.Arg_out
      | C.Phi _
      | C.Load _
      | C.Immed _ -> [dinf.src, offset]
      | _ ->
	  Log.printf 3 "Can't track: %s\n" (C.string_of_code dinf.src);
	  raise Untrackable
    with Not_found ->
      Log.printf 3 "Can't find def for %s\n"
	(C.string_of_code (C.SSAReg (fst use, snd use)));
      raise Untrackable in
  track use 0l

(* Improve a pointer. This might be done by:

     * walking through the chain of defs until we find a base register with a
       known type. [not yet implemented.]
     * finding a src which is "special" -- i.e. the stack pointer.
     * anything else?
*)

let improve_pointer vars defs ptr_reg offset =
  Log.printf 3 "Try to improve %s+%lx\n" (C.string_of_code ptr_reg) offset;
  try
    let def_chain =
      match ptr_reg with
        C.SSAReg regid -> track_pointer defs regid
      | C.Reg ptr -> [ptr_reg, 0l] in
    List.fold_left
      (fun best (src, def_offset) ->
        let offset_from_def = Int32.add def_offset offset in
        Log.printf 3 "Examine %s+%lx\n" (C.string_of_code src) offset_from_def;
	match src with
	  C.Nullary Irtypes.Incoming_sp -> src, offset_from_def
	| _ -> best)
      (ptr_reg, offset)
      def_chain
  with Untrackable ->
    ptr_reg, offset

exception Non_constant_offset

let ptr_plus_offset addr vars defs inforec =
  match addr with
    (C.SSAReg _ | C.Reg _ as ptr_reg) ->
      improve_pointer vars defs ptr_reg 0l
  | C.Binary (Irtypes.Add, (C.SSAReg _ | C.Reg _ as base), C.Immed imm) ->
      improve_pointer vars defs base imm
  | C.Binary (Irtypes.Sub, (C.SSAReg _ | C.Reg _ as base), C.Immed imm) ->
      improve_pointer vars defs base (Int32.neg imm)
  | _ -> raise Non_constant_offset

(* Try to build a snapshot of the stack at a given address (from debug
   info).  *)

let stack_for_addr vars addr =
  let cov = Coverage.create_coverage Int32.min_int 0l in
  List.iter
    (fun var ->
      match var.Function.var_location with
        None -> ()
      | Some loc ->
          try
	    let loc' = Dwarfreader.loc_for_addr addr loc in
	    match loc' with
	      `DW_OP_fbreg offs ->
		let range =
		  Coverage.Range (var, Int32.of_int offs,
				  Int32.of_int var.Function.var_size) in
		Coverage.add_range cov range
	    | `DW_OP_reg _ -> ()
	    | _ -> failwith "unexpected location/stack_for_addr"
	  with Not_found ->
	    ())
    vars;
  cov

let reg_or_ssareg_probably_pointer regid ct_for_cu inforec vartype_hash =
  match regid with
    C.SSAReg regid -> Typedb.probably_pointer ct_for_cu regid inforec
  | C.Reg reg ->
      begin match vartype_hash with
        Some vh ->
	  let vti = Hashtbl.find vh (Vartypes.T_reg reg) in
	  Ctype.pointer_type ct_for_cu vti.Vartypes.vt_type
      | None -> false
      end
  | _ -> failwith "Not reg or ssa reg"

let pointer_tracking blk_arr inforec dwarf_vars ?vartype_hash ctypes_for_cu =
  let defs = get_defs blk_arr in
  let stack_vars = ref IrPhiPlacement.R.empty in
  let blk_arr' = Array.map
    (fun blk ->
      let addr = ref None in
      let code' = CS.fold_left
        (fun codeseq stmt ->
	  match stmt with
	    C.Entity (CT.Insn_address ia) ->
	      addr := Some ia;
	      CS.snoc codeseq stmt
	  | C.Set (dst, C.Load (accsz, addr)) ->
	      begin try
		let base, offset =
		  ptr_plus_offset addr dwarf_vars defs inforec in
		let new_stmt =
		  try_rewrite_var dwarf_vars base (Int32.to_int offset)
				  stack_vars vartype_hash stmt
				  (`load (accsz, dst)) ctypes_for_cu in
		CS.snoc codeseq new_stmt
	      with Non_constant_offset ->
	        CS.snoc codeseq stmt
	      end
	  | C.Store (accsz, addr, src) ->
	      begin try
		let base, offset =
		  ptr_plus_offset addr dwarf_vars defs inforec in
		let new_stmt =
		  try_rewrite_var dwarf_vars base (Int32.to_int offset)
				  stack_vars vartype_hash stmt
				  (`store (accsz, src)) ctypes_for_cu in
		CS.snoc codeseq new_stmt
	      with Non_constant_offset ->
	        CS.snoc codeseq stmt
	      end
	  | C.Set (dst, src) ->
	      let src' = C.map
	        (fun addr ->
		  match addr with
		    (C.SSAReg _ | C.Reg _ as base)
		  | C.Binary (Irtypes.Add, (C.SSAReg _ | C.Reg _ as base),
			      C.Immed _)
		  | C.Binary (Irtypes.Sub, (C.SSAReg _ | C.Reg _ as base),
			      C.Immed _)
		      when reg_or_ssareg_probably_pointer base ctypes_for_cu
			     inforec vartype_hash ->
		      begin try
			let base, offset =
		          ptr_plus_offset addr dwarf_vars defs inforec in
			let new_var =
			  try_rewrite_var dwarf_vars base (Int32.to_int offset)
					  stack_vars vartype_hash addr `ssa_reg
					  ctypes_for_cu in
			new_var
		      with Non_constant_offset ->
		        addr
		      end
		  | x -> x)
		src in
	      CS.snoc codeseq (C.Set (dst, src'))
	  | x -> CS.snoc codeseq x)
	CS.empty
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr in
  blk_arr', !stack_vars

let maybe_stack_use cov ?accsz base offset =
  match base with
    C.Nullary Irtypes.Incoming_sp ->
      begin match accsz with
        None ->
	  Coverage.add_range cov (Coverage.Half_open ((), offset))
      | Some x ->
          let range_size =
	    match x with
	      Irtypes.U8 | Irtypes.S8 -> 1l
	    | Irtypes.U16 | Irtypes.S16 -> 2l
	    | Irtypes.Word -> 4l
	    | Irtypes.Dword -> 8l in
	  Coverage.add_range cov (Coverage.Range ((), offset, range_size))
      end
  | _ -> ()

let maybe_addressable base offset addr =
  match base with
    C.Nullary Irtypes.Incoming_sp ->
      let at_addr =
        match addr with
	  Some a -> Printf.sprintf " at %lx" a
	| None -> "" in
      Log.printf 3 "Addressable%s: %s+%ld\n" at_addr (C.string_of_code base)
		 offset;
  | _ -> ()

(* FIXME: Phi-node arguments might be classed as "escaping" too.  *)

let find_stack_references blk_arr inforec vars ctypes_for_cu =
  let defs = get_defs blk_arr in
  let cov = Coverage.create_coverage Int32.min_int Int32.max_int in
  let escaping_ref node addr =
    match node with
      C.Load (_, _) -> C.Protect node
    | C.Store (_, _, _) -> C.Protect node
    | C.Binary (Irtypes.Add, C.SSAReg (r, rn), C.Immed _)
    | C.Binary (Irtypes.Sub, C.SSAReg (r, rn), C.Immed _)
    | C.SSAReg (r, rn) ->
	let base, offset = ptr_plus_offset node vars defs inforec in
	maybe_addressable base offset addr;
	maybe_stack_use cov base offset;
	C.Protect node
    | _ -> node in
  Array.iter
    (fun blk ->
      let insn_addr = ref None in
      CS.iter
        (fun stmt ->
	  ignore (C.map
	    (fun node ->
	      try
	        match node with
		  C.Entity (CT.Insn_address ia) ->
	            insn_addr := Some ia;
		    node
		| C.Load (accsz, addr) ->
		    let base, offset = ptr_plus_offset addr vars defs inforec in
		    maybe_stack_use cov ~accsz base offset;
		    C.Protect node
		| C.Store (accsz, addr, src) ->
		    let base, offset = ptr_plus_offset addr vars defs inforec in
		    maybe_stack_use cov ~accsz base offset;
		    ignore (escaping_ref src !insn_addr);
		    C.Protect node
		| C.Set (dst, C.Phi phiargs) ->
		    Array.iter
		      (fun phiarg -> ignore (escaping_ref phiarg !insn_addr))
		      phiargs;
		    C.Protect node
		| _ -> node
	      with Non_constant_offset ->
	        C.Protect node)
	    ~ctl_fn:(fun ctlnode ->
	      match ctlnode with
		C.Call_ext (_, _, args, _, _) ->
	          (* Note any stack var which escapes (by having its address
		     taken) via being a function argument.  *)
	          ignore (C.map
		    (fun node -> escaping_ref node !insn_addr)
		    args);
		  ctlnode
	      | _ -> ctlnode)
	    stmt))
	blk.Block.code)
    blk_arr;
  cov

let maybe_replace_stackref accesstype orig base offset ranges =
  match base with
    C.Nullary Irtypes.Incoming_sp ->
      begin try
        let ival =
	  List.find (fun ival -> Coverage.interval_start ival = offset)
		    (Array.to_list ranges) in
	let var = C.Reg (CT.Stack (Int32.to_int offset)) in
	match accesstype with
	  `load -> var
	| `store src -> C.Set (var, src)
	| `ssa_reg -> C.Protect (C.Unary (Irtypes.Address_of, var))
      with Not_found ->
        orig
      end
  | _ -> orig

(* Call after pointer tracking, which might find actual variables for stack
   references.  *)

let replace_stack_references blk_arr coverage vars inforec =
  let stack_refs = ref IrPhiPlacement.R.empty
  and defs = get_defs blk_arr
  and ranges = Coverage.all_ranges coverage in
  let rewrite_escaping_ref node =
    match node with
      C.Load (_, _) -> C.Protect node
    | C.Store (_, _, _) -> C.Protect node
    | C.Binary (Irtypes.Add, C.SSAReg (r, rn), C.Immed _)
    | C.Binary (Irtypes.Sub, C.SSAReg (r, rn), C.Immed _)
    | C.SSAReg (r, rn) ->
        let base, offset = ptr_plus_offset node vars defs inforec in
	maybe_replace_stackref `ssa_reg node base offset ranges
    | _ -> node in
  let blk_arr' = Array.map
    (fun blk ->
      let code' = CS.map
        (fun stmt ->
	  C.map
	    (fun node ->
	      try
		match node with
	          C.Load (accsz, addr) ->
		    let base, offset = ptr_plus_offset addr vars defs inforec in
		    maybe_replace_stackref `load node base offset ranges
		| C.Store (accsz, addr, src) ->
	            let base, offset = ptr_plus_offset addr vars defs inforec in
		    let src' = rewrite_escaping_ref src in
	            maybe_replace_stackref (`store src') node base offset ranges
		| C.Set (dst, C.Phi phiargs) ->
		    let phiargs' =
		      Array.map
		        (fun phiarg -> rewrite_escaping_ref phiarg)
			phiargs in
		    C.Set (dst, C.Phi phiargs')
		| _ -> node
	      with Non_constant_offset ->
	        C.Protect node)
	    ~ctl_fn:(fun ctlnode ->
	      match ctlnode with
	        C.Call_ext (abi, addr, args, ret, retval) ->
		  let args' = C.map
		    (fun node -> rewrite_escaping_ref node)
		    args in
		  C.Call_ext (abi, addr, args', ret, retval)
	      | _ -> ctlnode)
	    stmt)
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr in
  Array.iter
    (fun blk ->
      CS.iter
        (fun stmt ->
	  C.iter
	    (fun node ->
	      match node with
	        C.Reg ((CT.Stack stkoff) as sref) ->
		  stack_refs := IrPhiPlacement.R.add sref !stack_refs;
	      | _ -> ())
	    stmt)
	blk.Block.code)
    blk_arr';
  blk_arr', !stack_refs
