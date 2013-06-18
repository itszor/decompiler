(* We have a lot of information about types of SSA registers from e.g.:
     - Incoming function arguments
     - Outgoing function arguments
     - Dwarf info about local variables
   Try to inject that type info here.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let inject_types blk_arr inforec ft =
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
			  (Typedb.Used_as_type fninf.Function.args.(i))
		    | _ -> ()
		  done
	      | _ -> ())
	    stmt)
	blk.Block.code)
    blk_arr
