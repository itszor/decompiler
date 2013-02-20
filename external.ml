open Binary_info

let load_lib filename =
  open_file filename

let lookup_function linf fnname =
  let sym = Symbols.find_named_symbol linf.symbols linf.strtab fnname in
  let sym_addr = sym.Elfreader.st_value in
  let cu_offset_for_sym = cu_offset_for_address linf sym_addr in
  let cu_inf = Hashtbl.find linf.cu_hash cu_offset_for_sym in
  let base_addr_for_cu = cu_inf.ci_baseaddr in
  let die = Hashtbl.find cu_inf.ci_dieaddr sym_addr in
  Function.function_type linf.debug_loc fnname die cu_inf.ci_dietab
			 cu_inf.ci_ctypes ~compunit_baseaddr:base_addr_for_cu
