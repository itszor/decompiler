open Defs

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

let string_of_offset offset =
  if offset < 0l then
    Int32.to_string offset
  else
    "+" ^ Int32.to_string offset

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

let first_src defs use =
  try
    let deflist = track_pointer defs use in
    match deflist with
      [] -> None
    | deflist -> Some (List.nth deflist (List.length deflist - 1))
  with Untrackable -> None

exception Not_constant_cfa_offset

let find_pointer_cfa_offset_equiv defs ptr_reg offset =
  Log.printf 4 "Looking for CFA offset for %s%s: " (C.string_of_code ptr_reg)
	     (string_of_offset offset);
  try
    let def_chain =
      match ptr_reg with
        C.SSAReg regid -> track_pointer defs regid
      | C.Reg ptr -> [ptr_reg, 0l]
      | _ -> failwith "bad register" in
    let _, def_offset =
      List.find
	(fun (src, _) ->
	  match src with
	    C.Nullary Irtypes.Incoming_sp -> true
	  | _ -> false)
	def_chain in
    let cfa_offset = Int32.add def_offset offset in
    Log.printf 4 "found, CFA%s.\n" (string_of_offset cfa_offset);
    cfa_offset    
  with Untrackable | Not_found ->
    Log.printf 4 "not found.\n";
    raise Not_constant_cfa_offset

(* Find the offset from the canonical frame address (CFA) for a given address
   ADDR, or raise Not_constant_cfa_offset if it doesn't have one (or we can't
   figure it out).  *)

let cfa_offset addr defs =
  match addr with
    (C.SSAReg _ | C.Reg _ as ptr_reg) ->
      find_pointer_cfa_offset_equiv defs ptr_reg 0l
  | C.Binary (Irtypes.Add, (C.SSAReg _ | C.Reg _ as base), C.Immed imm) ->
      find_pointer_cfa_offset_equiv defs base imm
  | C.Binary (Irtypes.Sub, (C.SSAReg _ | C.Reg _ as base), C.Immed imm) ->
      find_pointer_cfa_offset_equiv defs base (Int32.neg imm)
  | _ -> raise Not_constant_cfa_offset

(* Try to build a snapshot of the stack at a given address (from debug
   info).  *)

(*let stack_for_addr vars addr =
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
  cov*)

let maybe_stack_use cov ?accsz offset =
  match accsz with
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
	let offset = cfa_offset node defs in
	maybe_stack_use cov offset;
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
		    let offset = cfa_offset addr defs in
		    maybe_stack_use cov ~accsz offset;
		    C.Protect node
		| C.Store (accsz, addr, src) ->
		    let offset = cfa_offset addr defs in
		    maybe_stack_use cov ~accsz offset;
		    ignore (escaping_ref src !insn_addr);
		    C.Protect node
		| C.Set (dst, C.Phi phiargs) ->
		    Array.iter
		      (fun phiarg -> ignore (escaping_ref phiarg !insn_addr))
		      phiargs;
		    C.Protect node
		| _ -> node
	      with Not_constant_cfa_offset ->
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

module IrPhiPlacement = Phi.PhiPlacement (Ir.IrCT) (Ir.IrCS) (Ir.IrBS)

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
        let offset = cfa_offset node defs in
	maybe_replace_stackref `ssa_reg node (C.Nullary Irtypes.Incoming_sp)
			       offset ranges
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
		    let offset = cfa_offset addr defs in
		    maybe_replace_stackref `load node
					   (C.Nullary Irtypes.Incoming_sp)
					   offset ranges
		| C.Store (accsz, addr, src) ->
	            let offset = cfa_offset addr defs in
		    let src' = rewrite_escaping_ref src in
	            maybe_replace_stackref (`store src') node
					   (C.Nullary Irtypes.Incoming_sp)
					   offset ranges
		| C.Set (dst, C.Phi phiargs) ->
		    let phiargs' =
		      Array.map
		        (fun phiarg -> rewrite_escaping_ref phiarg)
			phiargs in
		    C.Set (dst, C.Phi phiargs')
		| _ -> node
	      with Not_constant_cfa_offset ->
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

type addressable_entity =
  {
    code : C.code;
    cfa_offset : int32;
    insn_addr : int32 option
  }

let string_of_optional_insn_addr = function
    Some x -> Printf.sprintf "address 0x%lx" x
  | None -> "unknown address"

(* Find addressable things on the stack.  This may vary according to the
   position in the function (because of e.g. local scopes).  Build up a hash
   table from insn addresses to addressable items?  *)

let find_addressable blk_arr inforec vars ctypes_for_cu defs =
  let addressable = ref [] in
  let maybe_addressable insn_addr thing code =
    try
      let offset = cfa_offset code defs in
      Log.printf 3 "%s %s equivalent to cfa offset %ld (at %s)\n" thing
		 (C.string_of_code code) offset
		 (string_of_optional_insn_addr insn_addr);
      let new_ent = {
        code = code;
	cfa_offset = offset;
	insn_addr = insn_addr
      } in
      addressable := new_ent :: !addressable
    with Not_constant_cfa_offset ->
      Log.printf 4 "%s %s not equivalent to cfa offset (at %s)\n" thing
		 (C.string_of_code code)
		 (string_of_optional_insn_addr insn_addr) in
  Array.iter
    (fun blk ->
      let insn_addr = ref None in
      ignore (CS.fold_left
        (fun _ stmt ->
	  ignore (C.map
	    (fun node ->
	      match node with
	        C.Entity (CT.Insn_address ia) ->
		  insn_addr := Some ia;
		  node
	      | C.Store (accsz, addr, src) ->
	          begin match accsz with
		    Irtypes.Word ->
		      maybe_addressable !insn_addr "stored value" src
		  | _ -> ()
		  end;
		  node
	      | C.Phi phiargs ->
	          Array.iter
		    (fun phiarg ->
		      try
			let def =
			  Hashtbl.find defs (Defs.ssa_id_of_code phiarg) in
			Log.printf 3 "Using %s for src of phi arg %s\n"
			  (string_of_optional_insn_addr def.Defs.src_insn_addr)
			  (C.string_of_code phiarg);
			maybe_addressable def.Defs.src_insn_addr "phi arg"
					  phiarg
		      with Not_found ->
			Log.printf 3 "No def for %s\n"
			  (C.string_of_code phiarg))
		    phiargs;
		  node
	      | C.Load (_, _) ->
	          (* If an address is indirected, it doesn't force it to be
		     addressable.  *)
	          C.Protect node
	      | _ -> node)
            ~ctl_fn:(fun ctlnode ->
	      match ctlnode with
		C.Call_ext (_, _, args, _, _) ->
		  ignore (C.map
		    (fun node ->
		      match node with
		        C.Nary (Irtypes.Fnargs, _) -> node
		      | C.Load (Irtypes.Word, addr) -> C.Protect node
		      | _ -> maybe_addressable !insn_addr "arg" node; node)
		    args);
		  ctlnode
	      | _ -> ctlnode)
	    stmt))
	()
	blk.Block.code))
    blk_arr;
  !addressable

module OffsetMap = Map.Make
  (struct
    type t = int
    let compare = compare
  end)

type stack_access_kind =
    Saved_caller_reg
  | Outgoing_arg
  | Incoming_arg
  | Local_var
  | Addressable_local_var
  | Addressable_anon_var
  | Local_var_or_spill_slot

exception Mixed

let kind_for_offset_word omap offset =
  let b1 = OffsetMap.find offset omap
  and b2 = OffsetMap.find (offset + 1) omap
  and b3 = OffsetMap.find (offset + 2) omap
  and b4 = OffsetMap.find (offset + 3) omap in
  if b1 = b2 && b2 = b3 && b3 = b4 then
    b1
  else
    raise Mixed

let letter_for_offset_word omap offset =
  try
    match kind_for_offset_word omap offset with
      Saved_caller_reg -> 'R'
    | Outgoing_arg -> 'A'
    | Incoming_arg -> 'I'
    | Local_var_or_spill_slot -> 'V'
    | Local_var -> 'L'
    | Addressable_local_var -> '&'
    | Addressable_anon_var -> '@'
  with
    Not_found -> '.'
  | Mixed -> '*'

let string_of_offsetmap om =
  let opt = function
    None -> "*"
  | Some x -> string_of_int x in
  let mini, maxi =
    OffsetMap.fold
      (fun key _ (lo, hi) ->
        begin match lo with
	  None -> Some key
	| Some lo -> Some (min key lo)
	end,
	begin match hi with
	  None -> Some key
	| Some hi -> Some (max key hi)
	end)
      om
      (None, None) in
  let prefix = Printf.sprintf "[%s...%s] " (opt maxi) (opt mini) in
  let buf = Buffer.create 5 in
  begin match mini, maxi with
    Some mini, Some maxi ->
      for i = (maxi - 3) / 4 downto mini / 4 do
	Buffer.add_char buf (letter_for_offset_word om (i * 4))
      done
  | _ -> ()
  end;
  prefix ^ (Buffer.contents buf)

let mix_kind offset old_kind new_kind =
  match old_kind, new_kind with
    Saved_caller_reg, Saved_caller_reg -> Saved_caller_reg
  | Saved_caller_reg, _
  | _, Saved_caller_reg ->
      Log.printf 3 "*** caller-saved reg collision, offset %d ***\n" offset;
      Saved_caller_reg
  | Outgoing_arg, Outgoing_arg -> Outgoing_arg
  | Outgoing_arg, _
  | _, Outgoing_arg ->
      Log.printf 3 "*** outgoing arg collision, offset %d ***\n" offset;
      Outgoing_arg
  | _, replacement -> replacement

let map_union a b =
  OffsetMap.merge
    (fun offset a_opt b_opt ->
      match a_opt, b_opt with
        Some x, Some y -> Some (mix_kind offset x y)
      | Some x, None -> Some x
      | None, Some y -> Some y
      | None, None -> None) a b

let rec record_kind_for_offset omap offset bytes kind =
  match bytes with
    0 -> omap
  | n ->
      begin try
        let existing = OffsetMap.find offset omap in
	let mixed = mix_kind offset existing kind in
	OffsetMap.add offset mixed (record_kind_for_offset omap (succ offset)
				     (pred bytes) kind)
      with Not_found ->
	OffsetMap.add offset kind (record_kind_for_offset omap (succ offset)
				    (pred bytes) kind)
      end

let seek_lower offsetmap cfa_offset sp_coverage insn_addr =
  let low_bound =
    Coverage.interval_type (Coverage.find_range sp_coverage insn_addr) in
  Log.printf 3 "low bound at %lx: %d\n" insn_addr low_bound;
  let rec find_lower offset =
    let pred_offset = pred offset in
    if offset <= low_bound || OffsetMap.mem pred_offset offsetmap then
      offset
    else
      find_lower pred_offset in
  find_lower (Int32.to_int cfa_offset)

let seek_higher offsetmap cfa_offset =
  let rec find_higher offset =
    let succ_offset = succ offset in
    if offset >= -1 || OffsetMap.mem succ_offset offsetmap then
      offset
    else
      find_higher succ_offset in
  find_higher (Int32.to_int cfa_offset)

let addressable_regions blkarr_offsetmap addressable sp_cov =
  let ht = Hashtbl.create 5 in
  List.iter
    (fun taken_address ->
      match taken_address.insn_addr with
        Some ia -> Hashtbl.add ht ia taken_address
      | None -> ())
    addressable;
  Array.fold_left
    (fun regions blk ->
      let _, regions' = CS.fold_left
        (fun (insn_addr, regions') (stmt, stmt_offsetmap) ->
	  match stmt with
	    C.Entity (CT.Insn_address ia) -> Some ia, regions'
	  | _ ->
	    let regions_ref = ref regions' in
	    begin match insn_addr with
	      None -> ()
	    | Some ia ->
	        while Hashtbl.mem ht ia do
	          let taken_address = Hashtbl.find ht ia in
		  if not (OffsetMap.mem (Int32.to_int taken_address.cfa_offset)
					!stmt_offsetmap) then begin
		    let upper_bound =
		      seek_higher !stmt_offsetmap taken_address.cfa_offset
		    and lower_bound =
		      seek_lower !stmt_offsetmap taken_address.cfa_offset
				 sp_cov ia in
		    Log.printf 3 "Anonymous addressable region, [%d...%d]\n"
		      lower_bound upper_bound;
		    regions_ref := (lower_bound, upper_bound) :: !regions_ref
		  end;
		  Hashtbl.remove ht ia
		done
	    end;
	    insn_addr, !regions_ref)
	(None, regions)
	blk.Block.code in
      regions')
    []
    blkarr_offsetmap

(* We might get overlapping addressable regions.  If two regions overlap, use
   the intersection of both.  *)

let prune_regions reg =
  let sorted_reg =
    List.sort (fun (a_lo, _) (b_lo, _) -> compare a_lo b_lo) reg in
  let rec prune = function
    [] -> []
  | [one] -> [one]
  | (a_lo, a_hi) :: (b_lo, b_hi) :: rest ->
      if b_lo > a_hi then
        (a_lo, a_hi) :: prune ((b_lo, b_hi) :: rest)
      else if b_lo >= a_lo && a_hi <= b_hi then
        prune ((b_lo, a_hi) :: rest)
      else
        prune ((b_lo, b_hi) :: rest) in
  let pruned = prune sorted_reg in
  Log.printf 3 "Pruned list:\n";
  List.iter
    (fun (lo, hi) -> Log.printf 3 "[%d...%d]\n" lo hi)
    pruned;
  pruned

(* Merge any anonymous stack blocks which have their address taken.  These must
   generally stay live throughout a function, but we can discount any points
   where the stack pointer register is above the block in question.  *)

let merge_anon_addressable blkarr_offsetmap sp_cov pruned_regions =
  Array.map
    (fun blk ->
      let _, newseq = CS.fold_left
        (fun (insn_addr, newseq) (stmt, stmt_offsetmap) ->
	  let ia_ref = ref insn_addr in
	  begin match stmt with
	    C.Entity (CT.Insn_address ia) -> ia_ref := Some ia
	  | _ -> ()
	  end;
	  let stmt_offsetmap' =
	    match !ia_ref with
	      None -> !stmt_offsetmap
	    | Some ia ->
	        try
		  let lo_stack =
		    Coverage.interval_type (Coverage.find_range sp_cov ia) in
		  List.fold_right
		    (fun (lo, hi) offsetmap ->
		      if lo >= lo_stack then
		        record_kind_for_offset offsetmap lo (hi - lo)
					       Addressable_anon_var
		      else
		        offsetmap)
		    pruned_regions
		    !stmt_offsetmap
		with Not_found ->
		  !stmt_offsetmap in
	  !ia_ref, CS.snoc newseq (stmt, ref stmt_offsetmap'))
	(None, CS.empty)
	blk.Block.code in
      { blk with Block.code = newseq })
    blkarr_offsetmap

type load_info =
  {
    load_cfa_offset : int32;
    load_insn_addr : int32 option
  }

type store_info =
  {
    store_cfa_offset : int32;
    store_insn_addr : int32 option
  }

type stack_access =
    Addressable_entity of addressable_entity
  | Load of load_info
  | Store of store_info

let anonymous_accesses blkarr_offsetmap dwarf_vars defs =
  Array.map
    (fun blk ->
      let codeseq' = CS.fold_left
        (fun newseq (stmt, stmt_offsetmap) ->
	  let stmt' = C.map
	    (fun node ->
	      match node with
	        C.Entity (CT.Insn_address _) -> node
	      | C.Load (accsz, addr) ->
	          begin try
		    let offset = cfa_offset addr defs in
		    Log.printf 3 "Load at cfa offset %ld (%c)\n" offset
		      (letter_for_offset_word !stmt_offsetmap
			(Int32.to_int offset));
		  with Not_constant_cfa_offset ->
		    ()
		  end;
	          node
	      | C.Store (accsz, addr, src) ->
	          begin try
		    let offset = cfa_offset addr defs in
		    Log.printf 3 "Store at cfa offset %ld (%c)\n" offset
		      (letter_for_offset_word !stmt_offsetmap
			(Int32.to_int offset));
		  with Not_constant_cfa_offset ->
		    ()
		  end;
		  node
	      | _ -> node)
	    stmt in
	  CS.snoc newseq (stmt', stmt_offsetmap))
	CS.empty
	blk.Block.code in
      { blk with Block.code = codeseq' })
    blkarr_offsetmap
