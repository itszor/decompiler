open Defs

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let string_of_i32offset offset =
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
      | C.Binary (CT.Add, (C.SSAReg (d, dn) as reg), C.Immed imm) ->
          let offset' = Int32.add offset imm in
	  (reg, offset') :: track (d, dn) offset'
      | C.Binary (CT.Sub, (C.SSAReg (d, dn) as reg), C.Immed imm) ->
          let offset' = Int32.sub offset imm in
	  (reg, offset') :: track (d, dn) offset'
      | C.Nullary CT.Callee_saved
      | C.Nullary CT.Special
      | C.Nullary CT.Incoming_sp
      (*| C.Nullary (CT.Arg_in _)*)
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
	     (string_of_i32offset offset);
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
	    C.Nullary CT.Incoming_sp -> true
	  | _ -> false)
	def_chain in
    let cfa_offset = Int32.add def_offset offset in
    Log.printf 4 "found, CFA%s.\n" (string_of_i32offset cfa_offset);
    cfa_offset    
  with Untrackable | Not_found ->
    Log.printf 4 "not found.\n";
    raise Not_constant_cfa_offset

(* Find the offset from the canonical frame address (CFA) for a given address
   ADDR, or raise Not_constant_cfa_offset if it doesn't have one (or we can't
   figure it out).
   FIXME: This has been superseded by initial_cfa_offsets below.  Update
   callers.  *)

let cfa_offset addr defs =
  match addr with
    (C.SSAReg _ | C.Reg _ as ptr_reg) ->
      find_pointer_cfa_offset_equiv defs ptr_reg 0l
  | C.Binary (CT.Add, (C.SSAReg _ | C.Reg _ as base), C.Immed imm) ->
      find_pointer_cfa_offset_equiv defs base imm
  | C.Binary (CT.Sub, (C.SSAReg _ | C.Reg _ as base), C.Immed imm) ->
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

type offset =
    Offset of int32
  | Induction of int32 * int32

let string_of_offset = function
    Offset x -> Int32.to_string x
  | Induction (st, ind) ->
      Printf.sprintf "%ld(%s...)" st (string_of_i32offset ind)

let string_of_insnaddr_opt = function
    None -> "<unknown>"
  | Some x -> Printf.sprintf "0x%lx" x

let string_of_i32s offs =
  String.concat ", " (List.map Int32.to_string offs)

module OffsetSet = Set.Make (struct
  type t = offset
  let compare = compare
end)

(* An anonymous variable, or part of one.  Adjacent anon_var_parts may need to
   be joined together (possibly with reduced lifespan) in order to preserve
   program semantics.  This is not done yet.  *)

type anon_var_part =
  {
    range : int * int;
    mutable live_at : BatISet.t;
    mutable mark : bool;
  }

type stack_slot =
  {
    (* For each byte offset into the slot, store access type and the byte
       offset into that type being acccessed.  *)
    slot_accesses : (CT.mem * int) list array;
    slot_size : int;
    mutable slot_live_at : BatISet.t
  }

type stack_access_kind =
    Saved_caller_reg_anon
  | Saved_caller_reg of stack_slot
  | Outgoing_arg_anon
  | Outgoing_arg of stack_slot
  | Incoming_arg of string
  | Local_var of Function.var
  | Addressable_local_var of Function.var
  | Addressable_anon_var of anon_var_part
  | Local_var_or_spill_slot of stack_slot

(* "Escape_by_foo" use the CFA_OFFSET field of ADDRESSABLE_ENTITY as the stack
   location whose address may escape from the current function.
   "Stack_foo" use the CFA_OFFSET for the stack slot which is loaded from or
   stored to.
   "Escape_by_stack_store foo" uses FOO as the stack slot being stored to, and
   CFA_OFFSET as the possibly-escaping address. It's possible (indirectly) for
   FOO to be part of an addressable object, also.  *)

type stack_access_type =
    Escape_by_store
  | Escape_by_stack_store of int32 list
  | Escape_by_fncall
  | Stack_load
  | Stack_store
  | Fncall

type addressable_entity =
  {
    code : C.code;
    access_type : stack_access_type;
    cfa_offsets : int32 list;
    insn_addr : int32 option;
    block : int;
    index : int;
    seq_no : int;
    reachable_forwards : Boolset.t;
    reachable_backwards : Boolset.t;
    offsetmap : stack_access_kind OffsetMap.t
  }

let string_of_access_type = function
    Escape_by_store -> "store stack address (not to stack)"
  | Escape_by_stack_store offs ->
      Printf.sprintf "store stack address (to stack offsets [%s])"
	(string_of_i32s offs)
  | Escape_by_fncall -> "stack address used as fn arg"
  | Stack_load -> "load from stack slot"
  | Stack_store -> "store to stack slot"
  | Fncall -> "fncall"

let access_is_escape = function
    Escape_by_store | Escape_by_stack_store _ | Escape_by_fncall
  | Fncall -> true
  | Stack_load | Stack_store -> false

let stack_slot acc =
  match acc.access_type with
    Stack_store | Stack_load -> acc.cfa_offsets
  | Escape_by_stack_store foo -> foo
  | _ -> raise Not_found

let string_of_optional_insn_addr = function
    Some x -> Printf.sprintf "address 0x%lx" x
  | None -> "unknown address"

module SSARegOffsetMap = Map.Make (struct
  type t = CT.reg * int
  let compare = compare
end)

module SSARegSet = Set.Make (struct
  type t = CT.reg * int
  let compare = compare
end)

let mark_offset ssareg offset map =
  if SSARegOffsetMap.mem ssareg map then
    let set = SSARegOffsetMap.find ssareg map in
    SSARegOffsetMap.add ssareg (OffsetSet.add offset set) map
  else
    SSARegOffsetMap.add ssareg (OffsetSet.singleton offset) map

let offset_marked_p ssareg offset map =
  SSARegOffsetMap.mem ssareg map
  && OffsetSet.mem offset (SSARegOffsetMap.find ssareg map)

let mark_offset_modified ssareg offset map =
  if offset_marked_p ssareg offset map then
    map, false
  else
    mark_offset ssareg offset map, true

let find_or_empty def map =
  try SSARegOffsetMap.find def map
  with Not_found -> OffsetSet.empty

let union_offsets_modified ssareg plus_set map =
  let set = find_or_empty ssareg map in
  let union_set = OffsetSet.union set plus_set in
  SSARegOffsetMap.add ssareg union_set map, not (OffsetSet.equal set union_set)

(*let phi_nodes blk_arr defs =
  let ht = Hashtbl.create 10 in
  let philist = Array.fold_right
    (fun blk acc ->
      CS.fold_right
        (fun (_, stmt, _) acc ->
	  match stmt with
	    C.Set (C.SSAReg dst, C.Phi phiargs) -> (dst, phiargs) :: acc
	  | _ -> acc)
	blk.Block.code
	acc)
    blk_arr
    [] in
  let offsetmap = ref SSARegOffsetMap.empty in
  List.iter
    (fun (dst, phiargs) ->
      Array.iter
        (fun phiarg ->
	  try
	    let offset = cfa_offset phiarg defs in
	    offsetmap := mark_offset dst offset !offsetmap
	  with Not_constant_cfa_offset -> ())
	phiargs)
    philist;
  let rec iter () =
    let made_changes = ref false in
    List.iter
      (fun (dst, phiargs) ->
        Array.iter
	  (function
	    C.SSAReg regsrc ->
	      let offsetmap', changed =
	        union_offsets_modified dst regsrc !offsetmap in
	      offsetmap := offsetmap';
	      made_changes := !made_changes || changed
	  | _ -> ())
	  phiargs)
      philist;
    if !made_changes then
      iter () in
  iter ();
  SSARegOffsetMap.iter
    (fun dst set ->
      Log.printf 3 "Phi node: %s: offsets [%s]\n"
        (Typedb.string_of_ssa_reg (fst dst) (snd dst))
	(String.concat ", " (List.map Int32.to_string
				      (OffsetSet.elements set))))
    !offsetmap;
  !offsetmap *)

let find_def_loops defs =
  let graph = Dgraph.make () in
  Hashtbl.iter
    (fun def info ->
      match info.src with
        C.SSAReg sreg -> Dgraph.add_edge def sreg graph
      | C.Binary ((CT.Add | CT.Sub), C.SSAReg reg, C.Immed _) ->
          Dgraph.add_edge def reg graph
      | C.Phi phiargs ->
          Array.iter
	    (function
	      C.SSAReg phireg -> Dgraph.add_edge def phireg graph
	    | _ -> ())
	    phiargs
      | C.Load _ | C.Call_ext _ -> ()
      | _ ->
	  C.iter
	    (function
	      C.SSAReg reg ->
	        Log.printf 3 "Adding dependency for %s on %s\n"
		  (Typedb.string_of_ssa_reg (fst def) (snd def))
		  (C.string_of_code info.src);
	        Dgraph.add_edge def reg graph
	    | _ -> ())
	    info.src)
    defs;
  let sccs = Dgraph.strongly_connected_components graph in
  Log.printf 3 "Defs which form loops:\n";
  let loopregs = List.fold_right
    (fun one_scc loopregs ->
      if List.length one_scc > 1 then begin
	Log.printf 3 "[%s]\n" (String.concat ", "
          (List.map (fun (r,rn) -> Typedb.string_of_ssa_reg r rn) one_scc));
	List.fold_right
	  (fun sreg acc -> SSARegSet.add sreg acc) one_scc loopregs
      end else
        loopregs)
    sccs
    SSARegSet.empty in
  if SSARegSet.is_empty loopregs then
    Log.printf 3 "(none)\n";
  loopregs

exception Unhandled

let track_all_stack_refs defs defloops =
  let offsetmap = ref SSARegOffsetMap.empty in
  let rec iter () =
    let changed = ref false in
    let mark_offset def offset =
      let offsetmap', this_changed =
        mark_offset_modified def offset !offsetmap in
      offsetmap := offsetmap';
      changed := !changed || this_changed
    and dup_mapped_offset def mapfn src =
      let mapped_src =
        OffsetSet.fold
          (fun elt map -> OffsetSet.add (mapfn elt) map)
	  (find_or_empty src !offsetmap)
	  OffsetSet.empty in
      let offsetmap', this_changed =
	union_offsets_modified def mapped_src !offsetmap in
      offsetmap := offsetmap';
      changed := !changed || this_changed in
    Hashtbl.iter
      (fun def info ->
        match info.src with
          C.Nullary CT.Incoming_sp ->
	    mark_offset def (Offset 0l)
	| C.SSAReg sreg ->
	    dup_mapped_offset def (fun x -> x) sreg
	| C.Binary (CT.Add, C.SSAReg reg, C.Immed imm) ->
            dup_mapped_offset def
	      (function
	        Offset x ->
		  if SSARegSet.mem def defloops then
		    Induction (x, imm)
		  else
		    Offset (Int32.add x imm)
	      | Induction (st, ind) when ind = imm ->
	          Induction (st, ind)
	      (* If this fails, we'll have to think of something smarter...  *)
	      | _ -> failwith "induction") reg
	| C.Binary (CT.Sub, C.SSAReg reg, C.Immed imm) ->
            dup_mapped_offset def
	      (function
	        Offset x ->
		  if SSARegSet.mem def defloops then
		    Induction (x, Int32.neg imm)
		  else
		    Offset (Int32.sub x imm)
	      | Induction (st, ind) when ind = Int32.neg imm ->
	          Induction (st, ind)
	      | _ -> failwith "induction") reg
	| C.Phi phiargs ->
            Array.iter
	      (function
		C.SSAReg phireg ->
		  dup_mapped_offset def (fun x -> x) phireg
	      | _ -> ())
	      phiargs
	| C.Load _ | C.Call_ext _ -> ()
        | _ ->
	    begin try
	      C.iter (function
	        C.SSAReg reg ->
		  let set = find_or_empty reg !offsetmap in
		  if OffsetSet.cardinal set > 0 then
		    raise Unhandled
	      | _ -> ()) info.src
	    with Unhandled ->
	      Log.printf 3 "Can't track: %s\n" (C.string_of_code info.src)
	    end)
      defs;
    if !changed then
      iter () in
  iter ();
  SSARegOffsetMap.iter
    (fun dst set ->
      Log.printf 3 "SSA reg %s: offsets [%s]\n"
        (Typedb.string_of_ssa_reg (fst dst) (snd dst))
	(String.concat ", " (List.map string_of_offset
				      (OffsetSet.elements set))))
    !offsetmap;
  !offsetmap

let cfa_offsets map_offsets_from_sreg addr =
  match addr with
    C.SSAReg sreg ->
      map_offsets_from_sreg (fun x -> x) sreg
  | C.Binary (CT.Add, C.SSAReg sreg, C.Immed imm) ->
      map_offsets_from_sreg (fun offs -> Int32.add offs imm) sreg
  | C.Binary (CT.Sub, C.SSAReg sreg, C.Immed imm) ->
      map_offsets_from_sreg (fun offs -> Int32.sub offs imm) sreg
  | _ -> raise Not_constant_cfa_offset

(* Find an int32 list of "initial" CFA offsets for a given address ADDR, i.e.
   those on the first iteration through the code (this might be a rather fuzzy
   concept...).  *)

let initial_cfa_offsets addr offsetmap =
  let map_offsets_from_sreg fn sreg =
    OffsetSet.fold
      (fun ofs acc ->
	match ofs with
	  Offset o -> fn o :: acc
	| Induction (st, ind) -> fn st :: acc)
      (find_or_empty sreg offsetmap)
      [] in
  cfa_offsets map_offsets_from_sreg addr

(* Find an offset list adjusted by any addition/subtraction in ADDR.  *)

let adjusted_cfa_offsets addr offsetmap =
  let map_offsets_from_sreg fn sreg =
    OffsetSet.fold
      (fun ofs acc ->
        match ofs with
	  Offset o -> Offset (fn o) :: acc
	| Induction (st, ind) -> Induction (fn st, ind) :: acc)
      (find_or_empty sreg offsetmap)
      [] in
  cfa_offsets map_offsets_from_sreg addr

(* Find a list of ADDRESSABLE_ENTITY nodes pertaining to addressability of
   stack locations.  *)

let find_addressable blk_arr inforec vars ctypes_for_cu defs def_cfa_offsets =
  let addressable = ref [] in
  let maybe_addressable stmt blkidx seq_no insn_addr thing code
			offsetmap =
    try
      let offsets = initial_cfa_offsets code def_cfa_offsets in
      match offsets with
        [] -> false
      | _ ->
	  Log.printf 3 "%s %s equivalent to cfa offsets [%s] (at %s)\n"
		     (string_of_access_type thing)
		     (C.string_of_code code) (string_of_i32s offsets)
		     (string_of_optional_insn_addr insn_addr);
	  let new_ent = {
            code = stmt;
	    cfa_offsets = offsets;
	    insn_addr = insn_addr;
	    access_type = thing;
	    block = blkidx;
	    index = seq_no;
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
  and create_node blkidx seq_no insn_addr thing code offsets offsetmap =
    match thing, offsets with
      (Stack_store | Stack_load), [] -> ()
    | _, _ ->
        let new_ent = {
	  code = code;
	  cfa_offsets = offsets;
	  insn_addr = insn_addr;
	  access_type = thing;
	  block = blkidx;
	  index = seq_no;
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
	        C.Store (CT.Word, addr, src) ->
	          begin try
		    let addr_offsets =
		      initial_cfa_offsets addr def_cfa_offsets in
		    let stored_addr_p =
		      maybe_addressable node idx seq_no insn_addr
			(Escape_by_stack_store addr_offsets) src
			offsetmap in
		    if not stored_addr_p then
		      create_node idx seq_no insn_addr Stack_store node
				  addr_offsets offsetmap
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
		    let addr_offsets =
		      initial_cfa_offsets addr def_cfa_offsets in
		    create_node idx seq_no insn_addr Stack_store node
				addr_offsets offsetmap
		  with Not_constant_cfa_offset -> ()
		  end;
		  node
	      | C.Load (accsz, addr) ->
	          begin try
		    let addr_offsets =
		      initial_cfa_offsets addr def_cfa_offsets in
		    create_node idx seq_no insn_addr Stack_load node
				addr_offsets offsetmap
		  with Not_constant_cfa_offset -> ()
		  end;
	          (* If an address is indirected, it doesn't force it to be
		     addressable.  *)
	          C.Protect node
	      | C.Call_ext (_, _, args) ->
		  ignore (C.map
		    (fun node ->
		      match node with
		        C.Nary (CT.Fnargs, _) -> node
		      | C.Load (CT.Word, addr) -> C.Protect node
		      | _ ->
			  ignore (maybe_addressable node idx seq_no
				    insn_addr Escape_by_fncall node offsetmap);
			  node)
		    args);
		  create_node idx seq_no insn_addr Fncall node []
			      offsetmap;
		  node
	      | _ -> node)
	    stmt);
	  succ seq_no)
	0
	blk.Block.code))
    blk_arr;
  !addressable

let virtual_exit_idx blk_arr =
  Block.find (fun blk -> blk.Block.id = BS.Virtual_exit) blk_arr

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
    C.Store (accsz, _, _) -> access_base + (CT.access_bytesize accsz)
  | C.Load (accsz, _) -> access_base + (CT.access_bytesize accsz)
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
  let maximise_bounds addr_taken_offset lo hi live_at reachable fwd rangelist =
    Boolset.fold_right
      (fun idx (lo, hi, live_at, rangelist) ->
        let targ_node = get_node idx in
	match targ_node.access_type with
	  Stack_load
	| Stack_store ->
	    let lo', hi', live_at' =
	      List.fold_right
	        (fun cfa_offset (lo'', hi'', live_at'') ->
		  let range_lo, range_hi =
		    if cfa_offset >= addr_taken_offset then
		      Int32.to_int addr_taken_offset,
		      beyond_stored_byte (Int32.to_int cfa_offset)
					 targ_node.code
		    else
		      Int32.to_int cfa_offset,
		      Int32.to_int addr_taken_offset in
		  if range_clear targ_node.offsetmap range_lo range_hi then
		    lo_opt lo'' range_lo, hi_opt hi'' range_hi,
		      BatISet.add targ_node.seq_no live_at''
		  else
		    lo'', hi'', live_at'')
	        targ_node.cfa_offsets
		(lo, hi, live_at) in
	    lo', hi', live_at', rangelist
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
		Log.printf 3 "Function may access block around %ld, bounds \
			      [%d...%d]\n" addr_taken_offset fnlo fnhi;
		let rangenode = {
		  range = fnlo, fnhi;
		  live_at = BatISet.singleton targ_node.seq_no;
		  mark = false
		} in
		lo, hi, live_at, rangenode :: rangelist
	    | None -> lo, hi, live_at, rangelist
	    end
	| _ -> lo, hi, live_at, rangelist)
      reachable
      (lo, hi, live_at, rangelist) in
  Array.fold_right
    (fun access_vec rangelist ->
      Vec.fold_right
	(fun access rangelist ->
	  match access.access_type with
	    Escape_by_store
	  | Escape_by_stack_store _ ->
	      List.fold_right
	        (fun cfa_offset rangelist ->
		  if not (OffsetMap.mem (Int32.to_int cfa_offset)
					access.offsetmap) then
		    let lo, hi, live_at, rangelist =
	              maximise_bounds cfa_offset None None BatISet.empty
				      access.reachable_forwards true
				      rangelist in
		    let lo, hi, live_at, rangelist =
	              maximise_bounds cfa_offset lo hi live_at
				      access.reachable_backwards false
				      rangelist in
		    begin match lo, hi with
	              Some lo, Some hi ->
			Log.printf 3
			  "Escape by store (at %s, CFA offset %s): reachable \
			   range [%d...%d]\n"
			  (string_of_insnaddr_opt access.insn_addr)
			  (string_of_i32offset cfa_offset)
			  lo hi;
			let rangenode = {
			  range = lo, hi;
			  live_at = live_at;
			  mark = false
			} in
			rangenode :: rangelist
		    | _ -> rangelist
		    end
		  else
	            rangelist)
		access.cfa_offsets
		rangelist
	  | Escape_by_fncall ->
	      List.fold_right
	        (fun cfa_offset rangelist ->
		  if not (OffsetMap.mem (Int32.to_int cfa_offset)
					access.offsetmap) then
		    match access.insn_addr with
	              Some insn_addr ->
			let lo = seek_lower access.offsetmap cfa_offset
					    sp_coverage insn_addr
			and hi = seek_higher access.offsetmap cfa_offset in
			Log.printf 3 "Escape by function arg (at %s, \
				      CFA offset %s): reachable range \
				      [%d...%d]\n"
				      (string_of_insnaddr_opt access.insn_addr)
				      (string_of_i32offset cfa_offset) lo hi;
			let rangenode = {
			  range = lo, hi;
			  live_at = BatISet.singleton access.seq_no;
			  mark = false
			} in
			let rangelist' = rangenode :: rangelist in
			(* The called function may stash the address we pass to
			   it, and subsequent function calls from the same
			   caller may access the same object.  *)
			let lo, hi, live_at, rangelist' =
			  maximise_bounds cfa_offset None None BatISet.empty
					  access.reachable_forwards true
					  rangelist' in
			let lo, hi, live_at, rangelist' =
			  maximise_bounds cfa_offset lo hi live_at
					  access.reachable_backwards false
					  rangelist' in
			begin match lo, hi with
			  Some lo, Some hi ->
			    let rangenode = {
			      range = lo, hi;
			      live_at = live_at;
			      mark = false
			    } in
			    rangenode :: rangelist'
			| _ -> rangelist'
			end
		    | None -> rangelist
		  else begin
	            Log.printf 4
		      "Not counting offset %ld for escape by function call\n"
		      cfa_offset;
	            rangelist
		  end)
		access.cfa_offsets
		rangelist
	  | _ -> rangelist)
	access_vec
	rangelist)
    arr
    []

let filter_ranges arr rangelist =
  Array.iter
    (fun access_vec ->
      Vec.iter
        (fun access ->
	  match access.access_type with
	    Escape_by_store
	  | Escape_by_stack_store _
	  | Escape_by_fncall ->
	      List.iter
	        (fun grange ->
		  let lo, hi = grange.range in
		  List.iter
		    (fun cfa_offset ->
		      let cfa_offset = Int32.to_int cfa_offset in
		      if not (OffsetMap.mem cfa_offset access.offsetmap)
		         && cfa_offset >= lo && cfa_offset < hi then
		        grange.mark <- true)
		    access.cfa_offsets)
		rangelist
	  | _ -> ())
	access_vec)
    arr;
  List.fold_right
    (fun ent outp ->
      if ent.mark then begin
        Log.printf 3 "Retaining range %d...%d\n" (fst ent.range)
		     (snd ent.range);
        ent :: outp
      end else begin
        Log.printf 3 "Dropping range %d...%d\n" (fst ent.range)
		   (snd ent.range);
	outp
      end)
    rangelist
    []

let dump_reachable ra =
  List.iter
    (fun ent ->
      let lo, hi = ent.range in
      Log.printf 3 "[%d...%d], live at [%s]\n" lo hi
	(String.concat ", " (List.map string_of_int
	  (BatISet.elements ent.live_at))))
    ra;
  Log.printf 3 "\n"

exception Mixed

let offsetmap_find_opt offset offsetmap =
  try Some (OffsetMap.find offset offsetmap)
  with Not_found -> None

let kind_for_offset_word omap offset =
  let b1 = offsetmap_find_opt offset omap
  and b2 = offsetmap_find_opt (offset + 1) omap
  and b3 = offsetmap_find_opt (offset + 2) omap
  and b4 = offsetmap_find_opt (offset + 3) omap in
  if b1 = b2 && b2 = b3 && b3 = b4 then
    b1
  else
    raise Mixed

let letter_for_offset_word omap offset =
  try
    match kind_for_offset_word omap offset with
      Some Saved_caller_reg_anon -> 'r'
    | Some (Saved_caller_reg _) -> 'R'
    | Some Outgoing_arg_anon -> 'a'
    | Some (Outgoing_arg _) -> 'A'
    | Some (Incoming_arg _) -> 'I'
    | Some (Local_var_or_spill_slot _) -> 'V'
    | Some (Local_var _) -> 'L'
    | Some (Addressable_local_var _) -> '&'
    | Some (Addressable_anon_var _) -> '@'
    | None -> '.'
  with Mixed -> '*'

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
      for i = maxi asr 2 downto mini asr 2 do
	Buffer.add_char buf (letter_for_offset_word om (i * 4))
      done
  | _ -> ()
  end;
  prefix ^ (Buffer.contents buf)

let string_of_offset_entry = function
    Some Saved_caller_reg_anon -> "anonymous saved caller reg"
  | Some (Saved_caller_reg _) -> "saved caller reg with stack slot"
  | Some Outgoing_arg_anon -> "anonymous outgoing arg"
  | Some (Outgoing_arg _) -> "outgoing arg with stack slot"
  | Some (Incoming_arg x) -> "incoming arg '" ^ x ^ "'"
  | Some (Local_var _) -> "local variable"
  | Some (Addressable_local_var _) -> "addressable local variable"
  | Some (Addressable_anon_var _) -> "anonymous addressable local var"
  | Some (Local_var_or_spill_slot _) -> "local var or spill slot"
  | None -> "unknown/unmapped"

let dump_addressable_table blk_arr addressable_tab =
  Log.printf 3 "Stack-access/addressable table:\n";
  Array.iteri
    (fun idx accesslist ->
      Log.printf 3 "Block %s:\n"
        (BS.string_of_blockref blk_arr.(idx).Block.id);
      Vec.iter
        (fun access ->
	  Log.printf 3 "seqno: %d  idx: %d  code: %s  cfa_offsets: [%s]  \
			access: %s\n"
	    access.seq_no access.index (C.string_of_code access.code)
	    (string_of_i32s access.cfa_offsets)
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
  let offstr () =
    if offsetlo = offsethi then string_of_int offsetlo
    else Printf.sprintf "%d...%d" offsetlo offsethi in
  match old_kind, new_kind with
    Saved_caller_reg_anon, Saved_caller_reg_anon -> Saved_caller_reg_anon
  | Saved_caller_reg_anon, Local_var_or_spill_slot slot ->
      Saved_caller_reg slot
  | Saved_caller_reg_anon, _
  | _, Saved_caller_reg_anon ->
      Log.printf 3 "*** caller-saved reg collision, offset %s ***\n"
        (offstr ());
      Saved_caller_reg_anon
  | Outgoing_arg_anon, Outgoing_arg_anon -> Outgoing_arg_anon
  | Outgoing_arg_anon, Local_var_or_spill_slot slot ->
      Outgoing_arg slot
  | Outgoing_arg_anon, _
  | _, Outgoing_arg_anon ->
      Log.printf 3 "*** outgoing arg collision, offset %s ***\n" (offstr ());
      Outgoing_arg_anon
  | Incoming_arg a, Local_var_or_spill_slot x ->
      (* Don't replace incoming args.  *)
      Incoming_arg a
  | _, replacement ->
      Log.printf 3 "*** replacing stack mapping, offset %s ***\n" (offstr ());
      replacement

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

let ranges_only ranges =
  List.map (fun r -> r.range) ranges

let overlaps_p lo1 hi1 lo2 hi2 =
  not (hi1 <= lo2 || hi2 <= lo1)

let reattach_liveness nonoverlapped_regions reachable =
  List.map
    (fun (r_lo, r_hi) ->
      let iset = List.fold_right
        (fun targ acc ->
	  let t_lo, t_hi = targ.range in
	  if overlaps_p r_lo r_hi t_lo t_hi then
	    BatISet.union targ.live_at acc
	  else
	    acc)
	reachable
	BatISet.empty in
      { range = (r_lo, r_hi); mark = false; live_at = iset })
    nonoverlapped_regions

(* The merge_* functions below need to access addressable_tab inside out now.
   Build a table from sequential indices (used by "live_at" from anon_var_part)
   to a block index and addressable entity.   *)

let create_access_by_seqno_htab addressable_tab =
  let atht = Hashtbl.create 5 in
  Array.iteri
    (fun blkidx accesslist ->
      Vec.iter
        (fun access ->
	  Hashtbl.add atht access.seq_no (blkidx, access))
	accesslist)
    addressable_tab;
  atht

(* Merge any anonymous stack blocks which have their address taken with a
   function's stack offset map.  These must generally stay live throughout a
   function, but we can discount any points where the stack pointer register is
   above the block in question.  *)

let merge_anon_addressable blkarr_offsetmap sp_cov atht pruned_regions =
  Array.map
    (fun blk ->
      let newseq, _ = CS.fold_left
        (fun (newseq, idx) (insn_addr, stmt, stmt_offsetmap) ->
	  let stmt_offsetmap' =
	    match insn_addr with
	      None -> stmt_offsetmap
	    | Some ia ->
	        try
		  let lo_stack =
		    Coverage.interval_type (Coverage.find_range sp_cov ia) in
		  List.fold_right
		    (fun region offsetmap ->
		      let lo, hi = region.range in
		      if lo >= lo_stack then begin
		        BatISet.fold
			  (fun seqno acc ->
			    let accblk, accinf = Hashtbl.find atht seqno in
			    if blk.Block.dfnum = accblk
			       && idx = accinf.index then begin
			      Log.printf 3
				"Merging region [%d...%d] in blk %s at idx %d\n"
			        lo hi (BS.string_of_blockref
				  blkarr_offsetmap.(accblk).Block.id)
				accinf.index;
		              record_kind_for_offset acc lo (hi - lo)
				(Addressable_anon_var region)
			    end else
			      acc)
			  region.live_at
			  offsetmap
		      end else
		        offsetmap)
		    pruned_regions
		    stmt_offsetmap
		with Not_found ->
		  stmt_offsetmap in
	  CS.snoc newseq (insn_addr, stmt, stmt_offsetmap'), succ idx)
	(CS.empty, 0)
	blk.Block.code in
      { blk with Block.code = newseq })
    blkarr_offsetmap

let stack_mapping_for_offset_opt stmt_offsetmap offset accsz =
  let bytesize = CT.access_bytesize accsz in
  let rec observe first idx =
    if idx = bytesize then
      first
    else begin
      let typ = offsetmap_find_opt (offset + idx) stmt_offsetmap in
      Log.printf 4 "offsetmap: %s offset: %d type: %s\n"
        (string_of_offsetmap stmt_offsetmap) (offset + idx)
	(string_of_offset_entry typ);
      match typ, first with
        Some t, Some f when t = f -> observe first (succ idx)
      | None, Some _
      | Some _, None
      | None, None -> observe first (succ idx)
      | _, _ ->
          Log.printf 1
	    "Mixed access at offset %d, byte size %d (first=%s, idx=%d, \
	     this=%s)\n"
	    offset bytesize (string_of_offset_entry first) idx
	    (string_of_offset_entry typ);
          raise Mixed
    end in
  let typ = offsetmap_find_opt offset stmt_offsetmap in
  Log.printf 4 "First byte offset=%d, type=%s\n" offset
	     (string_of_offset_entry typ);
  observe typ 1

let stack_mapping_for_offset stmt_offsetmap offset accsz =
  match stack_mapping_for_offset_opt stmt_offsetmap offset accsz with
    Some res -> res
  | None -> raise Not_found

(* Any stack bytes which are still accessed but are unknown can now be scanned
   and turned into local variables.  Some of these may genuinely have been local
   variables, and some may have been stack spill slots: we can't tell, though
   the latter will probably only use word-sized loads and stores.
   Create local var/spill slots for callee-saved registers also.

   First calculate a coverage data structure detailing *all* the ways a
   particular stack slot (CFA offset) is loaded/stored throughout the
   function.  *)

let find_local_or_spill_slot_coverage addressable_tab def_cfa_offsets =
  let coverage = Coverage.create_coverage 0l 0xffffffffl in
  let mark_access accsz addr =
    let bytesize = Int32.of_int (CT.access_bytesize accsz) in
    let offsets = adjusted_cfa_offsets addr def_cfa_offsets in
    List.iter
      (function
	Offset o ->
	  Coverage.add_range coverage (Coverage.Range (accsz, o, bytesize))
      | Induction (st, ind) when ind > 0l ->
	  Coverage.add_range coverage (Coverage.Half_open (accsz, st))
      | Induction (st, _) ->
	  Coverage.add_range coverage (Coverage.Range (accsz, st, bytesize)))
      offsets in
  for i = 0 to Array.length addressable_tab - 1 do
    Vec.iter
      (fun access ->
        match access.access_type with
	  Stack_load ->
	    begin match access.code with
	      C.Load (accsz, addr) -> mark_access accsz addr
	    | _ -> failwith "not load"
	    end
	| Stack_store ->
	    begin match access.code with
	      C.Store (accsz, addr, _) -> mark_access accsz addr
	    | _ -> failwith "not store"
	    end
	| _ -> ())
      addressable_tab.(i)
  done;
  coverage

(* Create a slot for a set of CFA (byte) offsets.  The slot_accesses field is
   indexed by byte number into the slot, and can be used to find all the ways
   that byte is accessed.  *)

let create_slot coverage offset bytesize =
  let arr = Array.create bytesize [] in
  for i = 0 to bytesize - 1 do
    let byte_offset = Int32.add offset (Int32.of_int i) in
    let stack =
      Coverage.find_range_stack coverage byte_offset in
    arr.(i) <- List.map
      (fun range ->
        let start = Coverage.interval_start range
	and rtype = Coverage.interval_type range in
	rtype, Int32.to_int (Int32.sub byte_offset start))
      stack
  done;
  { slot_accesses = arr; slot_size = bytesize; slot_live_at = BatISet.empty }

(* FIXME: The hidden assumption here (that only word loads and stores are used
   to access the stack) is not really true in the general case: for cases where
   this function would return false, we need to do something more
   sophisticated.  *)

let word_accesses_only stackslot =
  match stackslot.slot_accesses with
    [| [CT.Word, 0]; [CT.Word, 1];
       [CT.Word, 2]; [CT.Word, 3] |] -> true
  | _ -> false

exception Unbounded

(* Find the biggest closed range containing OFFSET in COVERAGE. Raise Unbounded
   if it is a half-open range, or Not_found if no range contains the offset.  *)

let slot_size coverage offset =
  let stack = Coverage.find_range_stack coverage offset in
  match stack with
    [] -> raise Not_found
  | _ ->
      begin match List.nth stack (List.length stack - 1) with
        Coverage.Range (_, sbase, sz) ->
	  Int32.to_int sbase, Int32.to_int sz
      | Coverage.Padded_range (_, sbase, _, sz) ->
	  Int32.to_int sbase, Int32.to_int sz
      | Coverage.Half_open (_, _) -> raise Unbounded
      end

(* Create a slot map (a BatIMap) from CFA byte offet ranges to the stack_slot
   structure which should be used for that range.  *)

let create_locals_or_spill_slots addressable_tab def_cfa_offsets coverage =
  (* Note physical equality here!  Otherwise (= equality) adjacent slots will
     get merged together, and we don't want that.  *)
  let slotmap = ref (BatIMap.empty ~eq:(==)) in
  let maybe_create_slot access accsz addr =
    let offsets = adjusted_cfa_offsets addr def_cfa_offsets in
    List.iter
      (function
        (* FIXME: This treatment of induction vars isn't going to be
	   sufficient.  *)
	Offset o | Induction (o, _) ->
	  try
	    let mapping =
	      stack_mapping_for_offset_opt access.offsetmap (Int32.to_int o)
					   accsz in
	    begin match mapping with
	      None
	    | Some Saved_caller_reg_anon
	    | Some Outgoing_arg_anon ->
		let sbase, ssize = slot_size coverage o in
		let slot =
		  if BatIMap.mem sbase !slotmap then
		    BatIMap.find sbase !slotmap
		  else begin
		    let slot' = create_slot coverage o ssize in
		    Log.printf 4
		      "Creating slot, offset %ld, base %d, size %d\n" o sbase
		      ssize;
		    (* BatI{Set,Map} ranges are inclusive.  *)
		    slotmap := BatIMap.add_range sbase (sbase + ssize - 1) slot'
						 !slotmap;
		    slot'
		  end in
		slot.slot_live_at <- BatISet.add access.seq_no slot.slot_live_at
	    | _ -> ()
	    end
	  with Mixed -> ())
      offsets in
  for i = 0 to Array.length addressable_tab - 1 do
    Vec.iter
      (fun access ->
        match access.access_type with
	  Stack_load ->
	    begin match access.code with
	      C.Load (accsz, addr) ->
	        maybe_create_slot access accsz addr
	    | _ -> failwith "not load"
	    end
	| Stack_store ->
	    begin match access.code with
	      C.Store (accsz, addr, _) ->
	        maybe_create_slot access accsz addr
	    | _ -> failwith "not store"
	    end
	| _ -> ())
     addressable_tab.(i)
  done;
  !slotmap

let dump_slotmap slotmap =
  Log.printf 3 "Slot map:\n";
  BatIMap.iter_range
    (fun lo hi slot ->
      Log.printf 3 "[%s...%s] %d bytes\n"
        (string_of_i32offset (Int32.of_int lo))
	(string_of_i32offset (Int32.of_int hi)) slot.slot_size)
    slotmap

(* Merge stack slots (as calculated by find_local_or_spill_slot_coverage and
   create_locals_or_stack_slots) with the stack offset maps for each stmt which
   should use those slots.  Modifies outgoing args and callee-saved register
   slots to point into the stack slot map also.  *)

let merge_spill_slots_or_local_vars blkarr_offsetmap atht slotmap =
  Array.map
    (fun blk ->
      let newseq, _ = CS.fold_left
        (fun (newseq, idx) (insn_addr, stmt, stmt_offsetmap) ->
	  let stmt_offsetmap' = BatIMap.fold_range
	    (fun lo hi slot stmt_offsetmap_acc ->
	      BatISet.fold
		(fun seqno so_acc ->
		  let accblk, accinf = Hashtbl.find atht seqno in
		  if blk.Block.dfnum = accblk
		     && idx = accinf.index then begin
		    Log.printf 3
		      "Merging spill slot/local var [%d...%d] at seqno %d\n"
		      lo hi seqno;
		    record_kind_for_offset so_acc lo (hi - lo + 1)
		      (Local_var_or_spill_slot slot)
		  end else
		    so_acc)
		slot.slot_live_at
		stmt_offsetmap_acc)
	    slotmap
	    stmt_offsetmap in
	  CS.snoc newseq (insn_addr, stmt, stmt_offsetmap'), succ idx)
	(CS.empty, 0)
	blk.Block.code in
      { blk with Block.code = newseq })
    blkarr_offsetmap

let stackvar_access base_expr typ offset ctypes_for_cu =
  if Ctype.aggregate_type ctypes_for_cu typ then
    Insn_to_ir.resolve_aggregate_access typ base_expr offset ctypes_for_cu
  else if Ctype.base_type_p typ && offset = 0 then
    base_expr
  else
    (* This can be other kinds of access, e.g. into an array.  FIXME!  *)
    C.Entity (CT.String_constant "!!BAD!!")

let rewrite_access make_access insn_addr accsz addr stmt_offsetmap
		   single node ftype ctypes_for_cu =
  try
    let mapping =
      stack_mapping_for_offset stmt_offsetmap (Int32.to_int single) accsz in
    match mapping with
      Local_var lv | Addressable_local_var lv ->
	begin match insn_addr, lv.Function.var_location with
          Some ia, Some loc ->
	    let cfa_base_opt = Locations.loc_cfa_offset_at_addr loc ia in
	    begin match cfa_base_opt with
	      Some cfa_base ->
		let offset_into_type = (Int32.to_int single) - cfa_base in
		let sv_acc =
		  stackvar_access (C.Entity (CT.Local_var lv.Function.var_name))
				  lv.Function.var_type offset_into_type
				  ctypes_for_cu in
		make_access sv_acc
	    | None -> node
	    end
	| _, _ -> node
	end
    | Saved_caller_reg slot | Outgoing_arg slot
    | Local_var_or_spill_slot slot ->
        if word_accesses_only slot then
          make_access (C.Reg (CT.Stack (Int32.to_int single)))
	else begin
	  Log.printf 3 "Non-word access for stack slot, ignoring (FIXME)\n";
	  node
	end
    | Incoming_arg argname ->
	let argnum = Function.arg_num_by_name ftype argname in
	let arg_accum = Eabi.make_arg_accum () in
	let loc = ref None in
	for arg = 0 to argnum do
	  loc := Some (Eabi.eabi_arg_loc ftype arg arg_accum ctypes_for_cu)
	done;
	begin try
	  match !loc with
	    Some loc ->
	      let sbe = Eabi.stack_base_equiv loc in
	      let sv_acc =
	        stackvar_access (C.Entity (CT.Arg_var argname))
		  ftype.Function.args.(argnum) (Int32.to_int single - sbe)
		  ctypes_for_cu in
	      make_access sv_acc
	  | None -> failwith "no location?"
	with Not_found ->
	  Log.printf 3 "Couldn't find stack base equiv for arg %d (%s)\n"
	    argnum argname;
	  node
	end
    | _ -> node
  with Not_found ->
    Log.printf 3 "Offset %ld not found in stack map %s\n" single
      (string_of_offsetmap stmt_offsetmap);
    node

let rewrite_load insn_addr accsz addr stmt_offsetmap single node
		 ftype ctypes_for_cu =
  rewrite_access (fun src -> src) insn_addr accsz addr stmt_offsetmap
		 single node ftype ctypes_for_cu

let rewrite_store insn_addr accsz addr src stmt_offsetmap single node
		  ftype ctypes_for_cu =
  rewrite_access (fun dst -> C.Set (dst, src)) insn_addr accsz addr
		 stmt_offsetmap single node ftype ctypes_for_cu

(* Ideally we want to get rid of all explicit references to the stack here.
   Is that possible?  *)

let rewrite_stack_refs blkarr_offsetmap def_cfa_offsets ftype ctypes_for_cu =
  Array.map
    (fun blk ->
      let newseq = CS.fold_left
	(fun newseq (insn_addr, stmt, stmt_offsetmap) ->
	  let stmt' = C.map
	    (fun node ->
	      match node with
		C.Load (accsz, addr) ->
	          begin try
		    let offsets = initial_cfa_offsets addr def_cfa_offsets in
		    match offsets with
		      [] -> C.Protect node
		    | [single] ->
			rewrite_load insn_addr accsz addr stmt_offsetmap
				     single node ftype ctypes_for_cu
		    | _ -> C.Protect node
		  with Not_constant_cfa_offset -> node
		  end
	      | C.Store (accsz, addr, src) ->
	          begin try
		    let offsets = initial_cfa_offsets addr def_cfa_offsets in
		    match offsets with
		      [] -> C.Protect node
		    | [single] ->
		        rewrite_store insn_addr accsz addr src stmt_offsetmap
				      single node ftype ctypes_for_cu
		    | _ -> C.Protect node
		  with Not_constant_cfa_offset -> node
		  end
	      | _ -> node)
	    stmt in
	  CS.snoc newseq (insn_addr, stmt', stmt_offsetmap))
	CS.empty
	blk.Block.code in
      { blk with Block.code = newseq })
    blkarr_offsetmap
