open Symbols

type mapping =
    ARM
  | Thumb
  | Data
  | Unknown

let get_mapping_symbols elfbits ehdr shdr_arr strtab symbols secname =
  let secnum = Elfreader.get_section_number elfbits ehdr shdr_arr secname in
  let syms_for_sec = symbols_for_section symbols secnum in
  let r = Coverage.create_coverage 0l 0xffffffffl in
  List.iter
    (fun sym ->
      if symbol_binding sym = STB_LOCAL
	 && symbol_type sym = STT_NOTYPE then begin
	let name = symbol_name sym strtab in
	match name with
	  "$a" | "$d" | "$t" ->
	    Coverage.add_range r
	      (Coverage.Half_open (sym, sym.Elfreader.st_value))
	| _ -> ()
      end)
    syms_for_sec;
  r

let mapping_for_addr mapping_syms strtab addr =
  let interv = Coverage.find_range mapping_syms addr in
  let sym = Coverage.interval_type interv in
  match symbol_name sym strtab with
    "$a" -> ARM
  | "$t" -> Thumb
  | "$d" -> Data
  | _ -> Unknown

(*

(* Retrieve mapping symbols for a given section, and return in reverse
   address order.  *)

let get_mapping_symbols elfbits ehdr shdr_arr strtab symbols secname =
  let secnum = Elfreader.get_section_number elfbits ehdr shdr_arr secname in
  let syms_for_sec = symbols_for_section symbols secnum in
  let syms =
    List.fold_right
      (fun sym mapping_syms ->
	if symbol_binding sym = STB_LOCAL
	   && symbol_type sym = STT_NOTYPE then begin
          let name = symbol_name sym strtab in
	  match name with
	    "$a" | "$d" | "$t" -> sym :: mapping_syms
	  | _ -> mapping_syms
	end else
          mapping_syms)
      syms_for_sec
      [] in
  List.sort (fun a b -> compare b.Elfreader.st_value a.Elfreader.st_value) syms

(* Find the mapping for address ADDR.  Address must be within a suitable range
   for the section the mapping symbols are associated with.  Linear search
   through symbols, but meh.  *)

let rec mapping_for_addr mapping_syms strtab addr =
  match mapping_syms with
    [] -> Unknown
  | sym::syms ->
      if addr >= sym.Elfreader.st_value then begin
	match symbol_name sym strtab with
	  "$a" -> ARM
	| "$t" -> Thumb
	| "$d" -> Data
	| _ -> Unknown
      end else
        mapping_for_addr syms strtab addr
*)

let string_of_mapping = function
    ARM -> "arm"
  | Thumb -> "thumb"
  | Data -> "data"
  | Unknown -> "unknown"
