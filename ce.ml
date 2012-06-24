open Defs

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

exception Unsafe_for_deletion

let rec def_chain defs x =
  try
    let dinf = Hashtbl.find defs x in
    if dinf.num_uses > 1 then
      raise Unsafe_for_deletion
    else match dinf.src with
      C.SSAReg (d, dn) -> x :: def_chain defs (d, dn)
    | C.Nullary Irtypes.Caller_saved
    | C.Nullary Irtypes.Special -> [x]
    | _ -> raise Unsafe_for_deletion
  with Not_found ->
    raise Unsafe_for_deletion

let remove_prologue_and_epilogue blk_arr =
  let defs = get_defs blk_arr in
  let defs_for_deletion = Hashtbl.create 10 in
  Array.iter
    (fun blk ->
      CS.iter
        (function
	  C.Set (C.Entity CT.Caller_restored, C.SSAReg (r, rn))
	| C.Control (C.CompJump_ext (CT.Branch_exchange, C.SSAReg (r, rn))) ->
	    begin try
	      let chain = def_chain defs (r, rn) in
	      Log.printf 3 "Can delete def chain: %s\n"
	        (String.concat ", "
		  (List.map (fun (r, rn) ->
		    C.string_of_code (C.SSAReg (r, rn))) chain));
	      let last = List.hd (List.rev chain) in
	      List.iter
	        (fun def ->
		  Hashtbl.replace defs_for_deletion def last)
		chain
	    with Unsafe_for_deletion ->
	      ()
	    end
	| _ -> ())
	blk.Block.code)
    blk_arr;
  Array.map
    (fun blk ->
      let code' = CS.fold_right
        (fun stmt acc ->
	  match stmt with
	    C.Set (C.Entity CT.Caller_restored, C.SSAReg (r, rn)) ->
	      if Hashtbl.mem defs_for_deletion (r, rn) then
	        acc
	      else
	        CS.cons stmt acc
	  | C.Set (C.SSAReg (d, dn), _) ->
	      if Hashtbl.mem defs_for_deletion (d, dn) then
	        acc
	      else
	        CS.cons stmt acc
	  | C.Control (C.CompJump_ext (CT.Branch_exchange, C.SSAReg (d, dn))) ->
	      begin try
	        let orig_def = Hashtbl.find defs_for_deletion (d, dn) in
		let orig_src = Hashtbl.find defs orig_def in
		Log.printf 3 "Original src for possible return: %s\n"
		  (C.string_of_code orig_src.src);
		match orig_src.src with
		  C.Nullary Irtypes.Special ->
		    let ret = C.Control (C.Return (C.Nullary Irtypes.Nop)) in
		    CS.cons ret acc
		| _ ->
		    CS.cons stmt acc
	      with Not_found ->
	        CS.cons stmt acc
	      end
	  | _ -> CS.cons stmt acc)
	blk.Block.code
	CS.empty in
      { blk with Block.code = code' })
    blk_arr
