(* We have a lot of information about types of SSA registers from e.g.:
     - Incoming function arguments
     - Outgoing function arguments
     - Dwarf info about local variables
   Try to inject that type info here.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

(* Transfer types from Dwarf info location information to SSA registers after
   the first SSA conversion pass.  NOTE: doesn't actually do anything yet!  *)

let early_inject_types blk_arr inforec dwarf_vars =
  Array.iter
    (fun blk ->
      ignore (CS.fold_left
        (fun insn_addr_opt stmt ->
	  let ia_ref = ref insn_addr_opt in
	  C.iter
	    (fun node ->
	      match node with
	        C.Entity (CT.Insn_address ia) -> ia_ref := Some ia
	      | C.SSAReg ((r, rn) as id) ->
		  begin match !ia_ref with
		    Some ia ->
		      List.iter
			(fun var ->
			  if Dwptrtracking.live_at_addr
			       var.Function.var_liveness ia then begin
			    let here_loc_opt =
			      match Locations.convert_dwarf_loclist_opt
				      var.Function.var_location with
				Some var_loc ->
				  Locations.valid_at_address ia var_loc
			      | None -> None in
			    match here_loc_opt with
			      Some (Locations.In (C.Reg n)) ->
			        if n = r then begin
				  Log.printf 3
				    "Register variable '%s %s' in %s\n"
				    (Ctype.string_of_ctype
				      var.Function.var_type)
				    var.Function.var_name
				    (C.string_of_code node);
				  Typedb.record_ltype inforec id
				    (Ltype.Ctype var.Function.var_type)
				end
			    | Some _ -> ()
			    | None -> ()
			  end)
			dwarf_vars
		  | None -> ()
		  end
	      | _ -> ())
	    stmt;
	  !ia_ref)
	None
	blk.Block.code))
    blk_arr

let inject_types blk_arr inforec =
  let open Ltype in
  Array.iter
    (fun blk ->
      CS.iter
        (fun stmt ->
	  C.iter  
	    (fun node ->
	      match node with
		C.Call_ext (_, CT.Finf_sym (symname, fninf, _),
			    C.Nary (CT.Fnargs, args)) ->
		  Log.printf 3 "Inject types for call to '%s'\n" symname;
		  for i = 0 to List.length args - 1 do
		    match List.nth args i with
		      C.SSAReg id ->
		        Typedb.record_info inforec.Typedb.infotag id
			  (Typedb.Used_as_type fninf.Function.args.(i));
			Typedb.record_ltype inforec id
			  (Ctype_compat fninf.Function.args.(i))
		    | _ -> ()
		  done
	      | _ -> ())
	    stmt)
	blk.Block.code)
    blk_arr
