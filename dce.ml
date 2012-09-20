open Defs

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

let remove_dead_code_once blk_arr =
  let made_change = ref false in
  let defs = get_defs blk_arr in
  let blk_arr' = Array.map
    (fun blk ->
      let code' = CS.map
        (fun stmt ->
	  C.map
	    (fun node ->
	      match node with
		C.Set (C.SSAReg regid, _) ->
		  begin try
	            let def = Hashtbl.find defs regid in
		    if def.num_uses > 0 then
		      C.Protect node
		    else begin
		      Log.printf 3 "Deleting set: %s\n"
			(C.string_of_code node);
		      made_change := true;
		      C.Nullary Irtypes.Nop
		    end
		  with Not_found ->
	            node
		  end
	      | _ -> node)
	    stmt)
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr in
  blk_arr', !made_change

let remove_dead_code blk_arr =
  let rec iter blk_arr =
    let new_blkarr, made_change = remove_dead_code_once blk_arr in
    if made_change then
      iter new_blkarr
    else
      new_blkarr in
  let blk_arr' = iter blk_arr in
  (* Remove nops created above.  *)
  Array.map
    (fun blk ->
      let code' = CS.fold_right
        (fun stmt acc ->
	  match stmt with
	    C.Nullary Irtypes.Nop -> acc
	  | _ -> CS.cons stmt acc)
	blk.Block.code
	CS.empty in
      { blk with Block.code = code' })
    blk_arr'
