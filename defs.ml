module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

type def_info = {
  src : C.code;
  src_insn_addr : int32 option;
  mutable num_uses : int;
  mutable ctype : Ctype.ctype option;
  mutable orig_name : string option
}

let count_uses blk_arr defs =
  Array.iter
    (fun blk ->
      CS.iter
        (fun stmt ->
	  ignore (C.map
	    (fun node ->
	      match node with
	        C.Set (C.Binary _, src) ->
		  (* This is an ugly hack concerning the representation used
		     for aggregate return. FIXME?  *)
		  node
	      | C.Set (dst, src) -> C.Set (C.Protect dst, src)
	      | C.SSAReg regid ->
	          begin try
		    let dinf = Hashtbl.find defs regid in
		    dinf.num_uses <- dinf.num_uses + 1;
		    node
		  with Not_found ->
		    node
		  end
	      | _ -> node)
	    stmt))
	blk.Block.code)
    blk_arr

let get_defs blk_arr =
  let ht = Hashtbl.create 10 in
  Array.iter
    (fun blk ->
      ignore (CS.fold_left
        (fun insn_addr stmt ->
	  let ia_ref = ref insn_addr in
	  C.iter
	    (function
	      C.Entity (CT.Insn_address ia) -> ia_ref := Some ia
	    | C.Set (C.SSAReg regid, src) ->
		let di = {
		  src = src;
		  src_insn_addr = !ia_ref;
		  ctype = None;
		  orig_name = None;
		  num_uses = 0
		} in
		Hashtbl.add ht regid di
	    | _ -> ())
	  stmt;
	  !ia_ref)
	None
	blk.Block.code))
    blk_arr;
  count_uses blk_arr ht;
  ht

let ssa_id_of_code = function
    C.SSAReg regid -> regid
  | _ -> raise Not_found
