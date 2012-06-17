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
	    Log.printf 3 "pc relative load: '%s'\n" (C.string_of_code x);
	    let addr = Int32.add loc imm in
	    let mapping = Mapping.mapping_for_addr mapping_syms strtab addr in
	    Log.printf 3 "mapping for addr 0x%lx is %s\n" addr
	      (Mapping.string_of_mapping mapping);
	    let section_num =
	      Elfreader.get_section_num_by_addr elfbits ehdr shdr_arr addr in
	    let section_name =
	      Elfreader.get_section_name elfbits ehdr shdr_arr section_num in
	    Log.printf 3 "address is in section %s " section_name;
	    let writable = Elfreader.section_writable shdr_arr.(section_num) in
	    if writable then
	      Log.printf 3 "(writable)\n"
	    else
	      Log.printf 3 "(read-only)\n";
	    let section = Elfreader.extract_section elfbits
			    shdr_arr.(section_num) in
	    let word = Elfreader.get_word shdr_arr.(section_num) section addr in
	    Log.printf 3 "loads word: %lx\n" word;
	    let pointer_p = Typedb.probably_pointer (rd, rdn) inforec in
	    let new_rhs =
	      if pointer_p then begin
		Log.printf 3 "register loaded is used as pointer\n";
		try
		  let sym =
		    Symbols.find_symbol_by_addr
		      ~filter:(fun symbol ->
			Symbols.symbol_type symbol <> Symbols.STT_NOTYPE
			|| Symbols.symbol_binding symbol <> Symbols.STB_LOCAL)
		      symbols word in
		  let symname = Symbols.symbol_name sym strtab in
		  Log.printf 3 "looks like symbol '%s'\n" symname;
		  C.Entity (CT.Symbol_addr (symname, sym))
		with Not_found ->
		  let pointed_to_sec_num =
		    Elfreader.get_section_num_by_addr elfbits ehdr shdr_arr
						      word in
		  let pointed_to_sec_name =
		    Elfreader.get_section_name elfbits ehdr shdr_arr
					       pointed_to_sec_num in
	          Log.printf 3 "pointer but no symbol for address\n";
		  Log.printf 3 "section name is %s\n" pointed_to_sec_name;
		  let sec_base =
		    shdr_arr.(pointed_to_sec_num).Elfreader.sh_addr in
		  Log.printf 3 "section base: %lx\n" sec_base;
		  let offset = Int32.sub word sec_base in
		  Log.printf 3 "offset into section %ld\n" offset;
		  (* FIXME: Special section+offset, then print section as
		     char array?  Better to use coverage -- split rodata up
		     into pieces, the best we can, after we've converted all
		     the code in the binary.  We can also make use of any
		     symbols defined in the section, which helpfully also have
		     sizes.  *)
		  C.Binary (Irtypes.Add,
			    C.Entity (CT.Section pointed_to_sec_name),
			    C.Immed offset)
	      end else begin
		Log.printf 3 "register loaded is not used as pointer\n";
		C.Immed word
	      end in
	      C.Set (C.SSAReg (rd, rdn), new_rhs)
	| x -> x)
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr
