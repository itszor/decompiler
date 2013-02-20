open Defs
open Ptrtracking

module BS = Ir.IrBS
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
		let offset = Ptrtracking.cfa_offset addr defs in
		let new_stmt =
		  try_rewrite_var dwarf_vars (C.Nullary Irtypes.Incoming_sp)
				  (Int32.to_int offset)
				  stack_vars vartype_hash stmt
				  (`load (accsz, dst)) ctypes_for_cu in
		CS.snoc codeseq new_stmt
	      with Ptrtracking.Not_constant_cfa_offset ->
	        CS.snoc codeseq stmt
	      end
	  | C.Store (accsz, addr, src) ->
	      begin try
		let offset = Ptrtracking.cfa_offset addr defs in
		let new_stmt =
		  try_rewrite_var dwarf_vars (C.Nullary Irtypes.Incoming_sp)
				  (Int32.to_int offset)
				  stack_vars vartype_hash stmt
				  (`store (accsz, src)) ctypes_for_cu in
		CS.snoc codeseq new_stmt
	      with Ptrtracking.Not_constant_cfa_offset ->
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
			let offset = Ptrtracking.cfa_offset addr defs in
			let new_var =
			  try_rewrite_var dwarf_vars
					  (C.Nullary Irtypes.Incoming_sp)
					  (Int32.to_int offset) stack_vars
					  vartype_hash addr `ssa_reg
					  ctypes_for_cu in
			new_var
		      with Ptrtracking.Not_constant_cfa_offset ->
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

let rec stack_address_within_var location_list insn_addr sp_offset var_size =
  match insn_addr with
    Some insn_addr' ->
      List.fold_right
        (fun location found ->
	  match location with
            Locations.Within_range (lo, hi, loc)
	      when insn_addr' >= lo && insn_addr' < hi ->
	      found || stack_address_within_var [loc] insn_addr sp_offset
						var_size
	  | Locations.Within_range (lo, hi, loc) ->
	      (*Log.printf 3 "Offset %ld not in %s, %lx not in range %lx-%lx\n" 
	        sp_offset (Location.string_of_location loc) insn_addr' lo hi;*)
	      found
	  | Locations.Parts _ -> failwith "unimplemented"
	  | Locations.In code ->
              begin match code with
		C.Reg (CT.Stack o) ->
		  found || (sp_offset >= Int32.of_int o
			    && sp_offset < Int32.of_int (o + var_size))
	      | _ -> found
	      end)
	location_list
	false
  | None -> false

let mark_addressable_vars blk_arr dwarf_vars addressable =
  List.iter
    (fun addressable_ent ->
      if access_is_escape addressable_ent.access_type then begin
	try
	  let var = List.find
            (fun var ->
	      match var.Function.var_location with
		Some loclist ->
		  let conv_loc = Locations.convert_dwarf_loclist loclist in
		  stack_address_within_var conv_loc
		    addressable_ent.Ptrtracking.insn_addr
		    addressable_ent.Ptrtracking.cfa_offset
		    var.Function.var_size
	      | None -> false)
	    dwarf_vars in
	  let iaddr_str =
	    Ptrtracking.string_of_optional_insn_addr
	      addressable_ent.Ptrtracking.insn_addr in
	  Log.printf 3 "Found var for CFA offset %ld (%s): %s\n"
	    addressable_ent.Ptrtracking.cfa_offset iaddr_str
	    var.Function.var_name;
	  (* Mark that the variable is addressable.  *)
	  var.Function.var_addressable <- true
	with Not_found ->
          Log.printf 3 "Can't find var for CFA offset %ld\n"
	    addressable_ent.Ptrtracking.cfa_offset
      end)
    addressable

let add_offsetmap_to_blkarr blkarr =
  Block.map_code
    (fun cseq ->
      let _, newseq = CS.fold_left
	(fun (insn_addr, newseq) stmt ->
          let ia_ref = ref insn_addr in
	  let newseq' =
	    match stmt with
	      C.Entity (CT.Insn_address ia) ->
		ia_ref := Some ia;
		newseq
	    | _ -> CS.snoc newseq (!ia_ref, stmt, OffsetMap.empty (=)) in
	  !ia_ref, newseq')
	(None, CS.empty)
	cseq in
      newseq)
    blkarr

let store defs accsz src offset offsetmap =
  let first_src = Ptrtracking.first_src defs src in
  Log.printf 4 "tracking %s for offset %ld\n"
    (Typedb.string_of_ssa_reg (fst src) (snd src)) offset;
  match first_src with
    None -> ()
  | Some ((C.Nullary (Irtypes.Special | Irtypes.Caller_saved) as fs), _) ->
      Log.printf 4 "first src %s\n" (C.string_of_code fs);
      offsetmap := record_kind_for_offset !offsetmap (Int32.to_int offset)
        (Irtypes.access_bytesize accsz) Saved_caller_reg
  | Some _ -> ()

let incoming defs accsz offset offsetmap =
  offsetmap := record_kind_for_offset !offsetmap (Int32.to_int offset)
    (Irtypes.access_bytesize accsz) Incoming_arg

let outgoing_arg defs accsz offset offsetmap =
  offsetmap := record_kind_for_offset !offsetmap (Int32.to_int offset)
    (Irtypes.access_bytesize accsz) Outgoing_arg

let unmark_outgoing_arg defs accsz offset offsetmap_ref =
  let rec scan bytes offset offsetmap =
    match bytes with
      0 -> offsetmap
    | n ->
	let offsetmap' =
	  try
	    match OffsetMap.find offset offsetmap with
	      Outgoing_arg -> OffsetMap.remove offset offsetmap
	    | _ -> offsetmap
	  with Not_found -> offsetmap in
	scan (pred bytes) (succ offset) offsetmap' in
  offsetmap_ref := scan (Irtypes.access_bytesize accsz) (Int32.to_int offset)
			!offsetmap_ref

(*let mark_addressable addressable_ent offsetmap =
  match addressable_ent.Ptrtracking.var with
    Some var ->
      offsetmap := record_kind_for_offset !offsetmap
	(Int32.to_int addressable_ent.Ptrtracking.cfa_offset)
	  var.Function.var_size
	Addressable_local_var
  | None -> ()*)

(* Merge OLDMAP with NEWMAP, returning the merged map and a boolean saying
   whether any significant changes happened.  *)

let merge_offsetmap oldmap newmap =
  let mergedmap = map_union oldmap newmap in
  if OffsetMap.equal (=) oldmap mergedmap then
    oldmap, false
  else
    mergedmap, true

let scan_stack_accesses blkarr dwarf_vars entrypoint defs =
  let num_blks = Array.length blkarr in
  let offsetmap_at_start = Array.make num_blks (OffsetMap.empty (=))
  and offsetmap_at_end = Array.make num_blks (OffsetMap.empty (=)) in
  let blkarr_offsetmap = add_offsetmap_to_blkarr blkarr in
  (* Propagate stores forwards.  *)
  let rec scan_f cur_offsetmap at =
    let made_change = ref false in
    Log.printf 3 "Propagating to block %d\n" at;
    let nom, chg = merge_offsetmap offsetmap_at_start.(at) cur_offsetmap in
    offsetmap_at_start.(at) <- nom;
    made_change := !made_change || chg;
    blkarr_offsetmap.(at).Block.visited <- true;
    let new_cs, final_offsetmap = CS.fold_left
      (fun (new_cs, offsetmap_acc) (insn_addr, stmt, stmt_offsetmap) ->
	let om_ref = ref offsetmap_acc in
        ignore (C.map
	  (fun node ->
	    try
              match node with
	        C.Store (accsz, addr, C.SSAReg src) ->
		  let offset = Ptrtracking.cfa_offset addr defs in
		  store defs accsz src offset om_ref;
		  C.Protect node
	      | C.Store (accsz, addr, C.Entity (CT.Arg_var _)) ->
		  let offset = Ptrtracking.cfa_offset addr defs in
	          incoming defs accsz offset om_ref;
		  C.Protect node
	      | _ -> node
	    with Ptrtracking.Not_constant_cfa_offset ->
	      C.Protect node)
	  stmt);
	CS.snoc new_cs (insn_addr, stmt, !om_ref), !om_ref)
      (CS.empty, cur_offsetmap)
      blkarr_offsetmap.(at).Block.code in
    blkarr_offsetmap.(at) <- { blkarr_offsetmap.(at) with Block.code = new_cs };
    let nom, chg = merge_offsetmap offsetmap_at_end.(at) final_offsetmap in
    offsetmap_at_end.(at) <- nom;
    made_change := !made_change || chg;
    List.iter
      (fun blk ->
        let dest_dfnum = blk.Block.dfnum in
        let dest_start = offsetmap_at_start.(dest_dfnum) in
	if !made_change || not blkarr_offsetmap.(dest_dfnum).Block.visited then
          scan_f final_offsetmap dest_dfnum)
      blkarr_offsetmap.(at).Block.successors in
  (* Propagate loads backwards.  *)
  let rec scan_b cur_offsetmap at =
    let made_change = ref false in
    Log.printf 3 "Propagating backwards to block %d\n" at;
    let nom, chg = merge_offsetmap offsetmap_at_end.(at) cur_offsetmap in
    offsetmap_at_end.(at) <- nom;
    made_change := !made_change || chg;
    Log.printf 3 "mark block %d visited\n" at;
    blkarr_offsetmap.(at).Block.visited <- true;
    let new_cs, start_offsetmap = CS.fold_right
      (fun (insn_addr, stmt, stmt_offsetmap) (new_cs, offsetmap_acc) ->
	let om_ref = ref offsetmap_acc
	and remove_offset_for_store = ref None in
	ignore (C.map
	  (fun node ->
	    try
	      match node with
	        C.Store (accsz, addr, C.SSAReg src) ->
	          let offset = Ptrtracking.cfa_offset addr defs in
		  remove_offset_for_store := Some (addr, accsz, offset);
	          C.Protect node
	      | _ -> node
	    with Ptrtracking.Not_constant_cfa_offset ->
	      C.Protect node)
	  ~ctl_fn:(fun node ->
	    match node with
	      C.Call_ext (_, _, args, _, _) ->
	        ignore (C.map
		  (fun node ->
		    try
		      match node with
			C.Load (accsz, addr) ->
			  let offset = Ptrtracking.cfa_offset addr defs in
			  outgoing_arg defs accsz offset om_ref;
			  C.Protect node
		      | _ -> node
		    with Ptrtracking.Not_constant_cfa_offset ->
		      C.Protect node)
		  args);
		node
	    | _ -> node)
	  stmt);
	let new_cs' = CS.cons (insn_addr, stmt, !om_ref) new_cs in
	begin match !remove_offset_for_store with
	  None -> ()
	| Some (addr, accsz, offset) ->
	    Log.printf 3 "unmarking for addr %s (offset %ld)\n"
	      (C.string_of_code addr) offset;
	    unmark_outgoing_arg defs accsz offset om_ref
	end;
	new_cs', !om_ref)
      blkarr_offsetmap.(at).Block.code
      (CS.empty, cur_offsetmap) in
    blkarr_offsetmap.(at) <- { blkarr_offsetmap.(at) with Block.code = new_cs };
    let nom, chg = merge_offsetmap offsetmap_at_start.(at) start_offsetmap in
    offsetmap_at_start.(at) <- nom;
    made_change := !made_change || chg;
    List.iter
      (fun blk ->
        let dest_dfnum = blk.Block.dfnum in
	let dest_end = offsetmap_at_end.(dest_dfnum) in
	if !made_change || not blkarr_offsetmap.(dest_dfnum).Block.visited then
	  scan_b start_offsetmap dest_dfnum)
      blkarr_offsetmap.(at).Block.predecessors in
  Block.clear_visited blkarr_offsetmap;
  scan_f (OffsetMap.empty (=)) entrypoint;
  Block.clear_visited blkarr_offsetmap;
  let v_exit = virtual_exit_idx blkarr_offsetmap in
  Log.printf 3 "Using virtual exit block index %d\n" v_exit;
  scan_b offsetmap_at_end.(v_exit) v_exit;
  blkarr_offsetmap

let log_liveness lv =
  Log.printf 3 "Liveness: ";
  let lstr = match lv with
    Function.Everywhere -> "everywhere"
  | Function.Lo_hi_range (l, h) -> Printf.sprintf "between %lx and %lx" l h
  | Function.Range_list rl ->
      Printf.sprintf "in ranges %s" (String.concat ", "
        (List.map (fun (l, h) -> Printf.sprintf "%lx-%lx" l h) rl)) in
  Log.printf 3 "%s\n" lstr

let live_at_addr liveness addr =
  match liveness with
    Function.Everywhere -> true
  | Function.Lo_hi_range (l, h) -> addr >= l && addr < h
  | Function.Range_list rl ->
      List.exists (fun (l, h) -> addr >= l && addr < h) rl

let merge_dwarf_vars blkarr_offsetmap dwarf_vars =
  List.fold_right
    (fun dwvar blkarr_offsetmap' ->
      Log.printf 3 "Merging dwarf var %s\n" dwvar.Function.var_name;
      let liveness = dwvar.Function.var_liveness in
      log_liveness liveness;
      let locs =
        Locations.convert_dwarf_loclist_opt dwvar.Function.var_location in
      Array.map
	(fun blk ->
	  let codeseq' = CS.fold_left
	    (fun newseq (insn_addr, stmt, stmt_offsetmap) ->
	      let om_ref = ref stmt_offsetmap in
	      begin match insn_addr with
		Some insn_addr ->
		  if live_at_addr liveness insn_addr then begin
		    List.iter
		      (fun loc ->
			let code_opt =
			  Locations.valid_at_address insn_addr loc in
			match code_opt with
			  Some (C.Reg (CT.Stack o)) ->
			    let typ =
			      if dwvar.Function.var_addressable then
				Addressable_local_var
			      else
				Local_var in
			    om_ref := record_kind_for_offset !om_ref o
					dwvar.Function.var_size typ
			| _ -> ())
		      locs
		  end
	      | None -> ()
	      end;
	      CS.snoc newseq (insn_addr, stmt, !om_ref))
	    CS.empty
	    blk.Block.code in
	  { blk with Block.code = codeseq' })
	blkarr_offsetmap')
    dwarf_vars
    blkarr_offsetmap

let dump_offsetmap_blkarr barr =
  Array.iter
    (fun block ->
      Log.printf 3 "block id \"%s\":\n" (BS.string_of_blockref block.Block.id);
      ignore (CS.fold_left
        (fun _ (insn_addr, code, offsets) ->
	  Log.printf 3 "%s\t%s\t%s\n"
	    (match insn_addr with
	      None -> "[...]"
	    | Some ia -> Printf.sprintf "[%.8lx]" ia) (C.string_of_code code)
	    (string_of_offsetmap offsets))
	()
        block.Block.code))
    barr
