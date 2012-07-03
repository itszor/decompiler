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

let try_rewrite_var vars offset stack_vars insn rewrite_as ctypes_for_cu =
  try
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
    match rewrite_as with
      `load (accsz, dst) ->
	C.Protect (C.Set (dst,
		     C.Load (accsz,
		       C.Unary (Irtypes.Aggr_member (kvar.Function.var_type,
		        			     aggr_access),
				C.Reg sv))))
    | `store (accsz, src) ->
        C.Protect (C.Store (accsz,
		     C.Unary (Irtypes.Aggr_member (kvar.Function.var_type,
						   aggr_access),
			      C.Reg sv),
		     src))
    | `ssa_reg ->
        C.Protect (C.Unary (Irtypes.Address_of,
	             C.Unary (Irtypes.Aggr_member (kvar.Function.var_type,
						   aggr_access),
			      C.Reg sv)))
  with Not_found ->
    insn

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
      | C.Nullary Irtypes.Arg_in
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
       known type.
     * finding a src which is "special" -- i.e. the stack pointer.
     * anything else?
*)

let improve_pointer vars defs ptr offset =
  let p, pn = ptr in
  Log.printf 3 "Try to improve %s+%lx\n" (Typedb.string_of_ssa_reg p pn) offset;
  try
    let def_chain = track_pointer defs ptr in
    List.fold_left
      (fun best (src, def_offset) ->
        let offset_from_def = Int32.add def_offset offset in
        Log.printf 3 "Examine %s+%lx\n" (C.string_of_code src) offset_from_def;
	match src with
	  C.Nullary Irtypes.Special -> src, offset_from_def
	| _ -> best)
      (C.SSAReg (p, pn), offset)
      def_chain
  with Untrackable ->
    C.SSAReg (p, pn), offset

let ptr_plus_offset addr vars defs inforec =
  match addr with
    C.SSAReg (r, rn) ->
      improve_pointer vars defs (r, rn) 0l
  | C.Binary (Irtypes.Add, C.SSAReg (r, rn), C.Immed imm) ->
      improve_pointer vars defs (r, rn) imm
  | C.Binary (Irtypes.Sub, C.SSAReg (r, rn), C.Immed imm) ->
      improve_pointer vars defs (r, rn) (Int32.neg imm)
  | _ -> raise Not_found

let pointer_tracking blk_arr inforec vars ctypes_for_cu =
  let defs = get_defs blk_arr in
  let stack_vars = ref IrPhiPlacement.R.empty in
  let blk_arr' = Array.map
    (fun blk ->
      let code' = CS.fold_right
        (fun stmt codeseq ->
	  match stmt with
	    C.Set (dst, C.Load (accsz, addr)) ->
	      let base, offset = ptr_plus_offset addr vars defs inforec in
	      let new_stmt = try_rewrite_var vars (Int32.to_int offset)
					     stack_vars stmt
					     (`load (accsz, dst))
					     ctypes_for_cu in
	      CS.cons new_stmt codeseq
	  | C.Store (accsz, addr, src) ->
	      let base, offset = ptr_plus_offset addr vars defs inforec in
	      let new_stmt = try_rewrite_var vars (Int32.to_int offset)
					     stack_vars stmt
					     (`store (accsz, src))
					     ctypes_for_cu in
	      CS.cons new_stmt codeseq
	  | C.Set (dst, src) ->
	      let src' = C.map
	        (fun addr ->
		  match addr with
		    C.SSAReg (r, rn)
		  | C.Binary (Irtypes.Add, C.SSAReg (r, rn), C.Immed _)
		  | C.Binary (Irtypes.Sub, C.SSAReg (r, rn), C.Immed _)
		      when Typedb.probably_pointer ctypes_for_cu (r, rn)
						   inforec ->
		      let base, offset =
		        ptr_plus_offset addr vars defs inforec in
		      let new_var = try_rewrite_var vars (Int32.to_int offset)
						    stack_vars addr `ssa_reg
						    ctypes_for_cu in
		      new_var
		  | x -> x)
		src in
	      CS.cons (C.Set (dst, src')) codeseq
	  | x -> CS.cons x codeseq)
	blk.Block.code
	CS.empty in
      { blk with Block.code = code' })
    blk_arr in
  blk_arr', !stack_vars
