type sym_type =
    STT_NOTYPE
  | STT_OBJECT
  | STT_FUNC
  | STT_SECTION
  | STT_FILE
  | STT_COMMON
  | STT_TLS
  | STT_GNU_IFUNC

type sym_binding =
    STB_LOCAL
  | STB_GLOBAL
  | STB_WEAK
  | STB_GNU_UNIQUE

let read_symbols symbits =
  let rec scan symbol_list symbits =
    match Bitstring.bitstring_length symbits with
      0 -> symbol_list
    | _ ->
      let sym, more = Elfreader.parse_sym symbits in
      scan (sym::symbol_list) more in
  List.rev (scan [] symbits)

let symbol_name symbol strtab =
  Elfreader.get_string strtab (Int32.to_int symbol.Elfreader.st_name)

let symbol_names symbols strtab =
  List.map
    (fun sym -> symbol_name sym strtab)
    symbols

let symbols_for_section symbols sec =
  List.filter (fun sym -> sym.Elfreader.st_shndx = sec) symbols

let sort_symbols symbols =
  List.sort
    (fun a b -> compare a.Elfreader.st_value b.Elfreader.st_value)
    symbols

exception Bad_symbol of string

let symbol_type symbol =
  let stype = symbol.Elfreader.st_info land 15 in
  match stype with
    0 -> STT_NOTYPE
  | 1 -> STT_OBJECT
  | 2 -> STT_FUNC
  | 3 -> STT_SECTION
  | 4 -> STT_FILE
  | 5 -> STT_COMMON
  | 6 -> STT_TLS
  | 10 -> STT_GNU_IFUNC
  | _ -> raise (Bad_symbol "type")

let symbol_binding symbol =
  let sbind = symbol.Elfreader.st_info lsr 4 in
  match sbind with
    0 -> STB_LOCAL
  | 1 -> STB_GLOBAL
  | 2 -> STB_WEAK
  | 10 -> STB_GNU_UNIQUE
  | _ -> raise (Bad_symbol "binding")

(* Find (the first) symbol named NAME in SYMBOLS.  *)
let find_named_symbol symbols strtab name =
  List.find
    (fun sym -> symbol_name sym strtab = name)
    symbols

let find_symbol_by_addr ?filter symbols addr =
  List.find
    (fun sym ->
      if sym.Elfreader.st_value = addr then
	match filter with
          None -> true
	| Some filter_fn -> filter_fn sym
      else
        false)
    symbols

let find_symbols_for_addr_range symbols addr_lo addr_hi =
  List.find_all
    (fun sym -> sym.Elfreader.st_value >= addr_lo
		&& sym.Elfreader.st_value < addr_hi)
    symbols
