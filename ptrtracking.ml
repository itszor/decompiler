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

(* "Escape_by_foo" use the CFA_OFFSET field of ADDRESSABLE_ENTITY as the stack
   location whose address may escape from the current function.
   "Stack_foo" use the CFA_OFFSET for the stack slot which is loaded from or
   stored to.
   "Escape_by_stack_store foo" uses FOO as the stack slot being stored to, and
   CFA_OFFSET as the possibly-escaping address. It's possible (indirectly) for
   FOO to be part of an addressable object, also.  *)

type stack_access_type =
    Escape_by_store
  | Escape_by_stack_store of int32
  | Escape_by_fncall
  | Escape_by_phiarg
  | Stack_load
  | Stack_store
  | Fncall

type addressable_entity =
  {
    code : C.code;
    access_type : stack_access_type;
    cfa_offset : int32;
    insn_addr : int32 option;
    block : int;
    seq_no : int;
    reachable_forwards : Boolset.t;
    reachable_backwards : Boolset.t;
    offsetmap : stack_access_kind OffsetMap.t
  }

let string_of_access_type = function
    Escape_by_store -> "store stack address (not to stack)"
  | Escape_by_stack_store offs ->
      Printf.sprintf "store stack address (to stack offset %ld)" offs
  | Escape_by_fncall -> "stack address used as fn arg"
  | Escape_by_phiarg -> "stack address used as phi arg"
  | Stack_load -> "load from stack slot"
  | Stack_store -> "store to stack slot"
  | Fncall -> "fncall"

let access_is_escape = function
    Escape_by_store | Escape_by_stack_store _ | Escape_by_fncall
  | Escape_by_phiarg | Fncall -> true
  | Stack_load | Stack_store -> false

let stack_slot acc =
  match acc.access_type with
    Stack_store | Stack_load -> acc.cfa_offset
  | Escape_by_stack_store foo -> foo
  | _ -> raise Not_found

let string_of_optional_insn_addr = function
    Some x -> Printf.sprintf "address 0x%lx" x
  | None -> "unknown address"

(* Find a list of ADDRESSABLE_ENTITY nodes pertaining to addressability of
   stack locations.  *)

let find_addressable blk_arr inforec vars ctypes_for_cu defs =
  let addressable = ref [] in
  let maybe_addressable blkidx seq_no insn_addr thing code offsetmap =
    try
      let offset = cfa_offset code defs in
      Log.printf 3 "%s %s equivalent to cfa offset %ld (at %s)\n"
		 (string_of_access_type thing)
		 (C.string_of_code code) offset
		 (string_of_optional_insn_addr insn_addr);
      let new_ent = {
        code = code;
	cfa_offset = offset;
	insn_addr = insn_addr;
	access_type = thing;
	block = blkidx;
	seq_no = seq_no;
	reachable_forwards = Boolset.empty;
	reachable_backwards = Boolset.empty;
	offsetmap = offsetmap
      } in
      addressable := new_ent :: !addressable;
      true
    with Not_constant_cfa_offset ->
      Log.printf 4 "%s %s not equivalent to cfa offset (at %s)\n"
		 (string_of_access_type thing)
		 (C.string_of_code code)
		 (string_of_optional_insn_addr insn_addr);
      false
  and create_node blkidx seq_no insn_addr thing code offset offsetmap =
    let new_ent = {
      code = code;
      cfa_offset = offset;
      insn_addr = insn_addr;
      access_type = thing;
      block = blkidx;
      seq_no = seq_no;
      reachable_forwards = Boolset.empty;
      reachable_backwards = Boolset.empty;
      offsetmap = offsetmap
    } in
    addressable := new_ent :: !addressable in
  Array.iteri
    (fun idx blk ->
      ignore (CS.fold_left
        (fun (insn_addr, seq_no) (stmt, offsetmap_ref) ->
	  let ia_ref = ref insn_addr in
	  ignore (C.map
	    (fun node ->
	      match node with
	        C.Entity (CT.Insn_address ia) ->
		  ia_ref := Some ia;
		  node
	      | C.Store (accsz, addr, src) when accsz = Irtypes.Word ->
	          begin try
		    let addr_offset = cfa_offset addr defs in
		    let stored_addr_p =
		      maybe_addressable idx seq_no !ia_ref
			(Escape_by_stack_store addr_offset) src
			!offsetmap_ref in
		    if not stored_addr_p then
		      create_node idx seq_no !ia_ref Stack_store addr
				  addr_offset !offsetmap_ref
		  with Not_constant_cfa_offset ->
		    ignore (maybe_addressable idx seq_no !ia_ref Escape_by_store
					      src !offsetmap_ref)
		  end;
		  node
	      | C.Store (_, addr, _) ->
		  (* Non-word-sized stores can't store an address (err, except
		     for doubleword stores might do).  Just note when it looks
		     like we're storing to a stack slot.  *)
	          begin try
		    let addr_offset = cfa_offset addr defs in
		    create_node idx seq_no !ia_ref Stack_store addr
				addr_offset !offsetmap_ref
		  with Not_constant_cfa_offset -> ()
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
			ignore (maybe_addressable idx seq_no
				  def.Defs.src_insn_addr Escape_by_phiarg
				  phiarg !offsetmap_ref)
		      with Not_found ->
			Log.printf 3 "No def for %s\n"
			  (C.string_of_code phiarg))
		    phiargs;
		  node
	      | C.Load (accsz, addr) ->
	          begin try
		    let addr_offset = cfa_offset addr defs in
		    create_node idx seq_no !ia_ref Stack_load addr addr_offset
				!offsetmap_ref
		  with Not_constant_cfa_offset -> ()
		  end;
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
		      | _ ->
			  ignore (maybe_addressable idx seq_no !ia_ref
				    Escape_by_fncall node !offsetmap_ref);
			  node)
		    args);
		  create_node idx seq_no !ia_ref Fncall (C.Nullary Irtypes.Nop)
			      0l !offsetmap_ref;
		  ctlnode
	      (* FIXME: Handle other external call types...  *)
	      | _ -> ctlnode)
	    stmt);
	  !ia_ref, succ seq_no)
	(None, 0)
	blk.Block.code))
    blk_arr;
  !addressable

let tabulate_addressable blk_arr addressable =
  let num_blocks = Array.length blk_arr in
  let arr = Array.make num_blocks [] in
  (* Partition ADDRESSABLE_ENTITIES into blocks.  *)
  List.iter
    (fun acc ->
      arr.(acc.block) <-
        { acc with reachable_forwards = Boolset.make num_blocks;
	  reachable_backwards = Boolset.make num_blocks } :: arr.(acc.block))
    addressable;
  (* Sort each block's ADDRESSABLE_ENTITIES into decreasing SEQ_NO order.  *)
  let arr = Array.map
    (fun acclist -> List.sort (fun a b -> compare b.seq_no a.seq_no) acclist)
    arr in
  (* Now renumber so that SEQ_NO are in monotonically increasing order across
     blocks (also reversing each list).  *)
  let midx = ref 0 in
  for i = 0 to num_blocks - 1 do
    let renlist, midx' = List.fold_left
      (fun (new_list, idx) acc ->
	{ acc with seq_no = idx } :: new_list, succ idx)
      ([], !midx)
      arr.(i) in
    arr.(i) <- renlist;
    midx := midx'
  done;
  arr

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
