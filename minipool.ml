(* Attempt to resolve minipool loads.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let minipool_resolve elfbits ehdr shdr_arr symbols mapping_syms strtab
		     blk_arr inforec =
  Array.map
    (fun blk ->
      let code' = CS.map
        (function
	  C.Set (C.SSAReg (rd, rdn), C.Load (Irtypes.Word,
		   C.Binary (Irtypes.Add, C.Entity (CT.PC loc),
					  C.Immed imm))) as x ->
	    Printf.printf "pc relative load: '%s'\n" (C.string_of_code x);
	    let addr = Int32.add loc imm in
	    let mapping = Mapping.mapping_for_addr mapping_syms strtab addr in
	    Printf.printf "mapping for addr 0x%lx is %s\n" addr
	      (Mapping.string_of_mapping mapping);
	    let section_num
	      = Elfreader.get_section_num_by_addr elfbits ehdr shdr_arr addr in
	    let section_name
	      = Elfreader.get_section_name elfbits ehdr shdr_arr section_num in
	    Printf.printf "address is in section %s " section_name;
	    let writable = Elfreader.section_writable shdr_arr.(section_num) in
	    if writable then
	      print_endline "(writable)"
	    else
	      print_endline "(read-only)";
	    let section = Elfreader.extract_section elfbits
			    shdr_arr.(section_num) in
	    let word = Elfreader.get_word shdr_arr.(section_num) section addr in
	    Printf.printf "loads word: %lx\n" word;
	    let pointer_p = Typedb.probably_pointer (rd, rdn) inforec in
	    let new_rhs =
	      if pointer_p then begin
		print_endline "register loaded is used as pointer";
		try
		  let sym = Symbols.find_symbol_by_addr symbols word in
		  let symname = Symbols.symbol_name sym strtab in
		  Printf.printf "looks like symbol '%s'\n" symname;
		  C.Entity (CT.Symbol_addr (symname, sym))
		with Not_found ->
	          print_endline
		    "pointer but no symbol for address, using immediate";
		  C.Immed word
	      end else begin
		print_endline "register loaded is not used as pointer";
		C.Immed word
	      end in
	      C.Set (C.SSAReg (rd, rdn), new_rhs)
	| x -> x)
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr
