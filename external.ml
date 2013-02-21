open Binary_info

let load_lib filename =
  Log.printf 2 "Loading library '%s'...\n" (Filename.basename filename);
  Log.flush ();
  {
    lib_name = filename;
    lib_info = open_file filename
  }

let find_in_lib linf fnname =
  let sym = Symbols.find_named_symbol linf.symbols linf.strtab fnname in
  let sym_addr = sym.Elfreader.st_value in
  let cu_offset_for_sym = cu_offset_for_address linf sym_addr in
  let cu_inf = Hashtbl.find linf.cu_hash cu_offset_for_sym in
  let base_addr_for_cu = cu_inf.ci_baseaddr in
  let die = Hashtbl.find cu_inf.ci_dieaddr sym_addr in
  cu_inf.ci_ctypes, Function.function_type linf.debug_loc fnname die
		      cu_inf.ci_dietab cu_inf.ci_ctypes
		      ~compunit_baseaddr:base_addr_for_cu

let dummy_ctypes =
  {
    Ctype.ct_typedefs = Hashtbl.create 1;
    ct_typetags = Hashtbl.create 1
  }

let lookup_function liblist fnname =
  let rec find = function
    [] ->
      begin try
        dummy_ctypes, Builtin.builtin_function_type fnname
      with Not_found ->
        Log.printf 1 "Unknown function '%s', substituting dummy\n" fnname;
	dummy_ctypes, Function.dummy_fn_info
      end
  | lib::libs ->
      begin try
        find_in_lib lib.lib_info fnname
      with Not_found ->
        find libs
      end in
  find liblist
