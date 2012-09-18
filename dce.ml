open Defs

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

let remove_dead_code_once blk_arr =
  let made_change = ref false in
  let defs = get_defs blk_arr in
  let blk_arr' = Array.map
    (fun blk ->
      let code' = CS.fold_right
        (fun stmt acc ->
	  match stmt with
	    C.Set (C.SSAReg (d, dn), _) ->
	      begin try
	        let def = Hashtbl.find defs (d, dn) in
		if def.num_uses > 0 then
		  CS.cons stmt acc
		else begin
		  Log.printf 3 "Deleting stmt: %s\n" (C.string_of_code stmt);
		  made_change := true;
		  acc
		end
	      with Not_found ->
	        CS.cons stmt acc
	      end
	  | _ -> CS.cons stmt acc)
	blk.Block.code
	CS.empty in
      { blk with Block.code = code' })
    blk_arr in
  blk_arr', !made_change

let rec remove_dead_code blk_arr =
  let new_blkarr, made_change = remove_dead_code_once blk_arr in
  if made_change then
    remove_dead_code new_blkarr
  else
    new_blkarr
