open Defs

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
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

module OffsetMap = struct
  include BatIMap

  let equal eq a b =
    forall2_range 
      (fun _ _ aopt bopt ->
	match aopt, bopt with
          None, None -> true
	| Some x, Some y when eq x y -> true
	| _, _ -> false) a b
end

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

(* For each phi node result (LHS), find a set of CFA-relative offsets.  *)

let phi_nodes blk_arr defs =
  let graph = Dgraph.make ()
  and ht = Hashtbl.create 10 in
  Array.iter
    (fun blk ->
      CS.iter
        (fun (insn_addr, stmt, offsetmap) ->
	  match stmt with
	    C.Set (C.SSAReg dst, C.Phi phiargs) ->
	      Array.iter
	        (function
		  C.SSAReg src -> Dgraph.add_edge dst src graph
		| _ -> ())
		phiargs;
	      Hashtbl.add ht dst phiargs
	  | _ -> ())
	blk.Block.code)
    blk_arr;
  let tgraph = Dgraph.tsort graph in
  let offsets_ht = Hashtbl.create 10 in
  List.iter
    (fun ((r, rn) as ssareg) ->
      let phiargs = Hashtbl.find ht ssareg in
      Array.iter
        (fun phiarg ->
	  try
	    let offset = cfa_offset phiarg defs in
	    Hashtbl.add offsets_ht ssareg offset;
	    begin match phiarg with
	      C.SSAReg regarg ->
		List.iter
		  (fun offset -> Hashtbl.add offsets_ht ssareg offset)
		  (Hashtbl.find_all offsets_ht regarg)
	    | _ -> ()
	    end
	  with Not_constant_cfa_offset -> ())
	phiargs)
    tgraph;
  List.iter
    (fun ssareg ->
      let offsets = Hashtbl.find_all offsets_ht ssareg in
      Log.printf 3 "Phi node: %s, offsets %s\n"
        (Typedb.string_of_ssa_reg (fst ssareg) (snd ssareg))
	(String.concat ", " (List.map Int32.to_string offsets)))
    tgraph

(* Find a list of ADDRESSABLE_ENTITY nodes pertaining to addressability of
   stack locations.  *)

let find_addressable blk_arr inforec vars ctypes_for_cu defs =
  let addressable = ref [] in
  let maybe_addressable stmt blkidx seq_no insn_addr thing code offsetmap =
    try
      let offset = cfa_offset code defs in
      Log.printf 3 "%s %s equivalent to cfa offset %ld (at %s)\n"
		 (string_of_access_type thing)
		 (C.string_of_code code) offset
		 (string_of_optional_insn_addr insn_addr);
      let new_ent = {
        code = stmt;
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
        (fun seq_no (insn_addr, stmt, offsetmap) ->
	  ignore (C.map
	    (fun node ->
	      match node with
	        C.Store (Irtypes.Word, addr, src) ->
	          begin try
		    let addr_offset = cfa_offset addr defs in
		    let stored_addr_p =
		      maybe_addressable node idx seq_no insn_addr
			(Escape_by_stack_store addr_offset) src
			offsetmap in
		    if not stored_addr_p then
		      create_node idx seq_no insn_addr Stack_store node
				  addr_offset offsetmap
		  with Not_constant_cfa_offset ->
		    ignore (maybe_addressable node idx seq_no insn_addr
					      Escape_by_store src
					      offsetmap)
		  end;
		  node
	      | C.Store (_, addr, _) ->
		  (* Non-word-sized stores can't store an address (err, except
		     for doubleword stores might do).  Just note when it looks
		     like we're storing to a stack slot.  *)
	          begin try
		    let addr_offset = cfa_offset addr defs in
		    create_node idx seq_no insn_addr Stack_store node
				addr_offset offsetmap
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
			ignore (maybe_addressable node idx seq_no
				  def.Defs.src_insn_addr Escape_by_phiarg
				  phiarg offsetmap)
		      with Not_found ->
			Log.printf 3 "No def for %s\n"
			  (C.string_of_code phiarg))
		    phiargs;
		  node
	      | C.Load (accsz, addr) ->
	          begin try
		    let addr_offset = cfa_offset addr defs in
		    create_node idx seq_no insn_addr Stack_load node addr_offset
				offsetmap
		  with Not_constant_cfa_offset -> ()
		  end;
	          (* If an address is indirected, it doesn't force it to be
		     addressable.  *)
	          C.Protect node
	      | C.Call_ext (_, _, args) ->
		  ignore (C.map
		    (fun node ->
		      match node with
		        C.Nary (Irtypes.Fnargs, _) -> node
		      | C.Load (Irtypes.Word, addr) -> C.Protect node
		      | _ ->
			  ignore (maybe_addressable node idx seq_no insn_addr
				    Escape_by_fncall node offsetmap);
			  node)
		    args);
		  create_node idx seq_no insn_addr Fncall node 0l offsetmap;
		  C.Protect node
	      | _ -> node)
	    stmt);
	  succ seq_no)
	0
	blk.Block.code))
    blk_arr;
  !addressable

let virtual_exit_idx blk_arr =
  Block.find (fun blk -> blk.Block.id = Irtypes.Virtual_exit) blk_arr

let tabulate_addressable blk_arr addressable =
  let num_blocks = Array.length blk_arr in
  let num_addressable = List.length addressable in
  let arr = Array.make num_blocks [] in
  (* Partition ADDRESSABLE_ENTITIES into blocks.  *)
  List.iter
    (fun acc ->
      arr.(acc.block) <-
        { acc with reachable_forwards = Boolset.make num_addressable;
	  reachable_backwards = Boolset.make num_addressable }
	:: arr.(acc.block))
    addressable;
  (* Sort each block's ADDRESSABLE_ENTITIES into decreasing SEQ_NO order.  *)
  let arr = Array.map
    (fun acclist -> List.sort (fun a b -> compare b.seq_no a.seq_no) acclist)
    arr in
  (* Now renumber so that SEQ_NO are in monotonically increasing order across
     blocks.  *)
  let midx = ref 0 in
  let arr2 = Array.make num_blocks Vec.empty in
  for i = 0 to num_blocks - 1 do
    let renlist, midx' = List.fold_right
      (fun acc (new_list, idx) ->
	Vec.snoc new_list { acc with seq_no = idx }, succ idx)
      arr.(i)
      (Vec.empty, !midx) in
    arr2.(i) <- renlist;
    midx := midx'
  done;
  let reachable_start =
    Array.init num_blocks (fun _ -> Boolset.make num_addressable)
  and reachable_end =
    Array.init num_blocks (fun _ -> Boolset.make num_addressable) in
  (* Analyze reachability.  First, do a backwards scan to determine forwards
     reachability for each access node.  *)
  let rec scan_backwards blkid cur_reachable =
    let at_end = Boolset.union cur_reachable reachable_end.(blkid) in
    let made_change = not (Boolset.equal at_end reachable_end.(blkid)) in
    reachable_end.(blkid) <- at_end;
    let at_start, newaccesslist =
      Vec.fold_right
	(fun access (reachable_bits, newlist) ->
	  let new_node =
	    { access with reachable_forwards =
		Boolset.union access.reachable_forwards reachable_bits }
	  and new_reachable =
	    Boolset.update reachable_bits access.seq_no true in
          new_reachable, Vec.snoc newlist new_node)
	arr2.(blkid)
	(at_end, Vec.empty) in
    let new_reachable = Boolset.union reachable_start.(blkid) at_start in
    let made_change = made_change ||
      not (Boolset.equal new_reachable reachable_start.(blkid)) in
    reachable_start.(blkid) <- new_reachable;
    arr2.(blkid) <- Vec.rev newaccesslist;
    blk_arr.(blkid).Block.visited <- true;
    List.iter
      (fun blk ->
        let idx = blk.Block.dfnum in
	if made_change || not blk_arr.(idx).Block.visited then
	  scan_backwards idx new_reachable)
      blk_arr.(blkid).Block.predecessors in
  Block.clear_visited blk_arr;
  let virtual_exit = virtual_exit_idx blk_arr in
  scan_backwards (virtual_exit) reachable_end.(virtual_exit);
  (* Now do a forwards scan to determine backwards reachability.  *)
  let reachable_start =
    Array.init num_blocks (fun _ -> Boolset.make num_addressable)
  and reachable_end =
    Array.init num_blocks (fun _ -> Boolset.make num_addressable) in
  let rec scan_forwards blkid cur_reachable =
    let at_start = Boolset.union cur_reachable reachable_start.(blkid) in
    let made_change = not (Boolset.equal at_start reachable_start.(blkid)) in
    reachable_start.(blkid) <- at_start;
    let at_end, newaccesslist =
      Vec.fold_left
        (fun (reachable_bits, newlist) access ->
	  let new_node =
	    { access with reachable_backwards =
	        Boolset.union access.reachable_backwards reachable_bits }
	  and new_reachable =
	    Boolset.update reachable_bits access.seq_no true in
	  new_reachable, Vec.snoc newlist new_node)
	(at_start, Vec.empty)
	arr2.(blkid) in
    let new_reachable = Boolset.union reachable_end.(blkid) at_end in
    let made_change = made_change
		      || not (Boolset.equal new_reachable
				reachable_end.(blkid)) in
    reachable_end.(blkid) <- new_reachable;
    arr2.(blkid) <- newaccesslist;
    blk_arr.(blkid).Block.visited <- true;
    List.iter
      (fun blk ->
        let idx = blk.Block.dfnum in
	if made_change || not blk_arr.(idx).Block.visited then
	  scan_forwards idx new_reachable)
      blk_arr.(blkid).Block.successors in
  Block.clear_visited blk_arr;
  scan_forwards 0 reachable_start.(0);
  arr2

type blk_offset =
  {
    block_num : int;
    offset : int
  }

(* Build an array mapping the sequential index number (of an access descriptor)
   to the block number (indexed into an array of vectors) and offset into the
   vector of that descriptor.  *)

let build_index_table arr =
  let len = Array.fold_right (fun vec ctr -> ctr + Vec.length vec) arr 0 in
  let table_idx = Array.make len { block_num = -1; offset = -1 } in
  Array.iteri
    (fun blkno vec ->
      Vec.iteri
        (fun offs access ->
	  table_idx.(access.seq_no) <- { block_num = blkno; offset = offs })
	vec)
    arr;
  table_idx

let beyond_stored_byte access_base store =
  match store with
    C.Store (accsz, _, _) -> access_base + (Irtypes.access_bytesize accsz)
  | C.Load (accsz, _) -> access_base + (Irtypes.access_bytesize accsz)
  | _ -> failwith "beyond_stored_byte"

let lo_opt lo new_lo =
  match lo with
    None -> Some new_lo
  | Some old_lo -> Some (min old_lo new_lo)

let hi_opt hi new_hi =
  match hi with
    None -> Some new_hi
  | Some old_hi -> Some (max old_hi new_hi)

let seek_lower offsetmap cfa_offset sp_coverage insn_addr =
  let low_bound =
    Coverage.interval_type (Coverage.find_range sp_coverage insn_addr) in
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

let reachable_addresses arr sp_coverage =
  let table_idx = build_index_table arr in
  let get_node idx =
    let entry = table_idx.(idx) in
    Vec.lookup arr.(entry.block_num) entry.offset in
  (* TRUE if offsetmap doesn't have any contents from LO to HI inclusive.  *)
  let range_clear offsetmap lo hi =
    let rec clear pos =
      if pos > hi then
        true
      else if OffsetMap.mem pos offsetmap then
        false
      else
        clear (succ pos) in
    clear lo in
  let maximise_bounds addr_taken_offset lo hi reachable fwd rangelist =
    Boolset.fold_right
      (fun idx (lo, hi, rangelist) ->
        let targ_node = get_node idx in
	match targ_node.access_type with
	  Stack_load
	| Stack_store ->
	    let range_lo, range_hi =
	      if targ_node.cfa_offset >= addr_taken_offset then
		Int32.to_int addr_taken_offset,
		beyond_stored_byte (Int32.to_int targ_node.cfa_offset)
				   targ_node.code
	      else
		Int32.to_int targ_node.cfa_offset,
		Int32.to_int addr_taken_offset in
	    if range_clear targ_node.offsetmap range_lo range_hi then
	      lo_opt lo range_lo, hi_opt hi range_hi, rangelist
	    else
	      lo, hi, rangelist
	| Fncall when fwd ->
	    (* If we've stored a stack address somewhere, then we call a
	       function, the function might write anywhere in the object whose
	       address was taken.  Functions called before the address was
	       stored are irrelevant though.  *)
	    begin match targ_node.insn_addr with
	      Some insn_addr ->
	        let fnlo = seek_lower targ_node.offsetmap addr_taken_offset
				      sp_coverage insn_addr
		and fnhi = seek_higher targ_node.offsetmap addr_taken_offset in
		lo, hi, (fnlo, fnhi) :: rangelist
	    | None -> lo, hi, rangelist
	    end
	| _ -> lo, hi, rangelist)
      reachable
      (lo, hi, rangelist) in
  Array.fold_right
    (fun access_vec rangelist ->
      Vec.fold_right
	(fun access rangelist ->
	  match access.access_type with
	    Escape_by_store
	  | Escape_by_stack_store _ ->
	      if not (OffsetMap.mem (Int32.to_int access.cfa_offset)
				    access.offsetmap) then
		let lo, hi, rangelist =
	          maximise_bounds access.cfa_offset None None
				  access.reachable_forwards true rangelist in
		let lo, hi, rangelist =
	          maximise_bounds access.cfa_offset lo hi
				  access.reachable_backwards false rangelist in
		begin match lo, hi with
	          Some lo, Some hi ->
		    Log.printf 3 "Escape by store: reachable range [%d...%d]\n"
		      lo hi;
		    (lo, hi) :: rangelist
		| _ -> rangelist
		end
	      else
	        rangelist
	  | Escape_by_fncall ->
	      if not (OffsetMap.mem (Int32.to_int access.cfa_offset)
				    access.offsetmap) then
		match access.insn_addr with
	          Some insn_addr ->
		    let lo = seek_lower access.offsetmap access.cfa_offset
					sp_coverage insn_addr
		    and hi = seek_higher access.offsetmap access.cfa_offset in
		    Log.printf 3 "Escape by function call: reachable range \
				 [%d...%d]\n" lo hi;
		    (lo, hi) :: rangelist
		| None -> rangelist
	      else begin
	        Log.printf 4 "Not counting offset %ld for escape by function \
			      call\n" access.cfa_offset;
	        rangelist
	      end
	  | Escape_by_phiarg ->
	      Log.printf 3 "Warning: escape by phi arg not implemented\n";
	      (* FIXME: This isn't sufficient, I don't think.  *)
	      rangelist
	  | _ -> rangelist)
	access_vec
	rangelist)
    arr
    []

let dump_reachable ra =
  List.iter
    (fun (lo, hi) -> Log.printf 3 "[%d...%d] " lo hi)
    ra;
  Log.printf 3 "\n"

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

let dump_addressable_table blk_arr addressable_tab =
  Log.printf 3 "Stack-access/addressable table:\n";
  Array.iteri
    (fun idx accesslist ->
      Log.printf 3 "Block %s:\n"
        (BS.string_of_blockref blk_arr.(idx).Block.id);
      Vec.iter
        (fun access ->
	  Log.printf 3 "seqno: %d  code: %s  cfa_offset: %ld  access: %s\n"
	    access.seq_no (C.string_of_code access.code) access.cfa_offset
	    (string_of_access_type access.access_type);
	  Log.printf 4 "stack: %s\n" (string_of_offsetmap access.offsetmap);
	  Log.printf 5 "reachable fwd: [%s]\n"
	    (String.concat ", " (List.map string_of_int
	      (Boolset.elements access.reachable_forwards)));
	  Log.printf 5 "reachable bwd: [%s]\n\n"
	    (String.concat ", " (List.map string_of_int
	      (Boolset.elements access.reachable_backwards))))
	accesslist;
      Log.printf 3 "\n")
    addressable_tab

let mix_kind offsetlo offsethi old_kind new_kind =
  let offstr =
    if offsetlo = offsethi then string_of_int offsetlo
    else Printf.sprintf "%d...%d" offsetlo offsethi in
  match old_kind, new_kind with
    Saved_caller_reg, Saved_caller_reg -> Saved_caller_reg
  | Saved_caller_reg, _
  | _, Saved_caller_reg ->
      Log.printf 3 "*** caller-saved reg collision, offset %s ***\n" offstr;
      Saved_caller_reg
  | Outgoing_arg, Outgoing_arg -> Outgoing_arg
  | Outgoing_arg, _
  | _, Outgoing_arg ->
      Log.printf 3 "*** outgoing arg collision, offset %s ***\n" offstr;
      Outgoing_arg
  | _, replacement -> replacement

let map_union a b =
  OffsetMap.merge ~eq:(=)
    (fun lo hi a_opt b_opt ->
      match a_opt, b_opt with
        Some x, Some y -> Some (mix_kind lo hi x y)
      | Some x, None -> Some x
      | None, Some y -> Some y
      | None, None -> None) a b

let rec record_kind_for_offset omap offset bytes kind =
  match bytes with
    0 -> omap
  | n ->
      begin try
        let existing = OffsetMap.find offset omap in
	let mixed = mix_kind offset offset existing kind in
	OffsetMap.add offset mixed (record_kind_for_offset omap (succ offset)
				     (pred bytes) kind)
      with Not_found ->
	OffsetMap.add offset kind (record_kind_for_offset omap (succ offset)
				    (pred bytes) kind)
      end

(* Given a set of possibly overlapping (start,end) ranges, find a new set of
   ranges which covers the same regions (using a non-zero "winding rule"), but
   which does not contain any overlaps.  *)

let nonoverlapping_ranges r =
  let rs = List.sort (fun (a, _) (b, _) -> compare a b)
    (List.fold_left (fun acc (l,h) -> (l, true) :: (h, false) :: acc) [] r) in
  let rec build eqto depth acc = function
    [] -> acc
  | (r, true) :: rest ->
      if r = eqto then build r (succ depth) acc rest
      else if depth > 0 then build r (succ depth) ((eqto, r) :: acc) rest
      else build r (succ depth) acc rest
  | (r, false) :: rest ->
      if r = eqto then build r (pred depth) acc rest
      else if depth > 0 then build r (pred depth) ((eqto, r) :: acc) rest
      else build r (pred depth) acc rest
  and start depth acc = function
    [] -> acc
  | (r, true) :: rest -> build r (succ depth) acc rest
  | (r, false) :: rest -> build r (pred depth) acc rest in
  let res = start 0 [] rs in
  if List.length res > 0 then begin
    Log.printf 3 "De-overlapped list:\n";
    List.iter
      (fun (lo, hi) -> Log.printf 3 "[%d...%d]\n" lo hi)
      res
  end;
  res

(* Merge any anonymous stack blocks which have their address taken with a
   function's stack offset map.  These must generally stay live throughout a
   function, but we can discount any points where the stack pointer register is
   above the block in question.  *)

let merge_anon_addressable blkarr_offsetmap sp_cov pruned_regions =
  Array.map
    (fun blk ->
      let newseq = CS.fold_left
        (fun newseq (insn_addr, stmt, stmt_offsetmap) ->
	  let stmt_offsetmap' =
	    match insn_addr with
	      None -> stmt_offsetmap
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
		    stmt_offsetmap
		with Not_found ->
		  stmt_offsetmap in
	  CS.snoc newseq (insn_addr, stmt, stmt_offsetmap'))
	CS.empty
	blk.Block.code in
      { blk with Block.code = newseq })
    blkarr_offsetmap
