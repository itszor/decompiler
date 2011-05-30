exception Elf_read_error of string

type elf_ehdr =
{
  e_type : int;
  e_machine : int;
  e_version: int32;
  e_entry : int32;
  e_phoff : int32;
  e_shoff : int32;
  e_flags : int32;
  e_ehsize : int;
  e_phentsize : int;
  e_phnum : int;
  e_shentsize : int;
  e_shnum : int;
  e_shstrndx : int
}

let parse_ehdr elfbits =
  bitmatch elfbits with
  | { 0x7f : 8; "ELF" : 24 : string;	(* ELF magic number.  *)
      _ : 12 * 8 : bitstring;		(* ELF identifier.  *)
      e_type : 16 : littleendian;	(* Object file type.  *)
      e_machine : 16 : littleendian;	(* Architecture.  *)
      e_version : 32 : littleendian;	(* Object file version.  *)
      e_entry : 32 : littleendian;	(* Entry point.  *)
      e_phoff : 32 : littleendian;	(* Program header table file offset.  *)
      e_shoff : 32 : littleendian;	(* Section header table offset.  *)
      e_flags : 32 : littleendian;	(* Processor-specific flags.  *)
      e_ehsize : 16 : littleendian;	(* ELF header size in bytes.  *)
      e_phentsize : 16 : littleendian;	(* Program header table entry size.  *)
      e_phnum : 16 : littleendian;	(* PHT entry count.  *)
      e_shentsize : 16 : littleendian;	(* Section header table entry size.  *)
      e_shnum : 16 : littleendian;	(* SHT entry count.  *)
      e_shstrndx : 16 : littleendian } -> (* Section header string table.  *)
      { e_type = e_type;
	e_machine = e_machine;
	e_version = e_version;
	e_entry = e_entry;
	e_phoff = e_phoff;
	e_shoff = e_shoff;
	e_flags = e_flags;
	e_ehsize = e_ehsize;
	e_phentsize = e_phentsize;
	e_phnum = e_phnum;
	e_shentsize = e_shentsize;
	e_shnum = e_shnum;
	e_shstrndx = e_shstrndx }
  | { _ } ->
      raise (Elf_read_error "Can't parse Elf Ehdr")

type elf_shdr =
{
  sh_name : int32;
  sh_type : int32;
  sh_flags : int32;
  sh_addr : int32;
  sh_offset : int32;
  sh_size : int32;
  sh_link : int32;
  sh_info : int32;
  sh_addralign : int32;
  sh_entsize : int32
}

let parse_shdr elfbits =
  bitmatch elfbits with
    { sh_name : 32 : littleendian;	(* Section name (string tbl index).  *)
      sh_type : 32 : littleendian;	(* Section type.  *)
      sh_flags : 32 : littleendian;	(* Section flags.  *)
      sh_addr : 32 : littleendian;	(* Section virtual addr at
					   execution. *)
      sh_offset : 32 : littleendian;	(* Section file offset.  *)
      sh_size : 32 : littleendian;	(* Section size in bytes.  *)
      sh_link : 32 : littleendian;	(* Link to another section.  *)
      sh_info : 32 : littleendian;	(* Additional section information.  *)
      sh_addralign : 32 : littleendian;	(* Section alignment.  *)
      sh_entsize : 32 : littleendian } ->
					(* Entry size if section holds
					   table.  *)
      { sh_name = sh_name;
        sh_type = sh_type;
	sh_flags = sh_flags;
	sh_addr = sh_addr;
	sh_offset = sh_offset;
	sh_size = sh_size;
	sh_link = sh_link;
	sh_info = sh_info;
	sh_addralign = sh_addralign;
	sh_entsize = sh_entsize }
  | { _ } ->
      raise (Elf_read_error "Can't parse Elf Shdr")

type elf_sym =
{
  st_name : int32;
  st_value : int32;
  st_size : int32;
  st_info : int;
  st_other : int;
  st_shndx : int
}

let parse_sym elfbits =
  bitmatch elfbits with
    { st_name : 32 : littleendian;	(* Symbol name (string tbl index).  *)
      st_value : 32 : littleendian;	(* Symbol value.  *)
      st_size : 32 : littleendian;	(* Symbol size.  *)
      st_info : 8 : littleendian;	(* Symbol type and binding.  *)
      st_other : 8 : littleendian;	(* Symbol visibility.  *)
      st_shndx : 16 : littleendian } ->	(* Section index.  *)
      { st_name = st_name;
        st_value = st_value;
	st_size = st_size;
	st_info = st_info;
	st_other = st_other;
	st_shndx = st_shndx }
  | { _ } ->
      raise (Elf_read_error "Can't parse symbol")

type elf_syminfo =
{
  si_boundto : int;
  si_flags : int
}

let parse_syminfo elfbits =
  bitmatch elfbits with
    { si_boundto : 16 : littleendian;	(* Direct bindings, symbol bound to.  *)
      si_flags : 16 : littleendian } ->	(* Per symbol flags.  *)
      { si_boundto = si_boundto;
        si_flags = si_flags }
  | { _ } ->
      raise (Elf_read_error "Can't parse syminfo")

type elf_rel =
{
  rel_offset : int32;
  rel_info : int32
}

let parse_rel elfbits =
  bitmatch elfbits with
    { r_offset : 32 : littleendian;	(* Address.  *)
      r_info : 32 : littleendian } ->	(* Relocation type and symbol index.  *)
      { rel_offset = r_offset;
        rel_info = r_info }
  | { _ } ->
      raise (Elf_read_error "Can't parse rel")

type elf_rela =
{
  rela_offset : int32;
  rela_info : int32;
  rela_addend : int32
}

let parse_rela elfbits =
  bitmatch elfbits with
    { r_offset : 32 : littleendian;	(* Address.  *)
      r_info : 32 : littleendian;	(* Relocation type and symbol index.  *)
      r_addend : 32 : littleendian } ->	(* Addend.  *)
      { rela_offset = r_offset;
        rela_info = r_info;
	rela_addend = r_addend }
  | { _ } ->
      raise (Elf_read_error "Can't parse rela")

type elf_phdr =
{
  p_type : int32;
  p_offset : int32;
  p_vaddr : int32;
  p_paddr : int32;
  p_filesz : int32;
  p_memsz : int32;
  p_flags : int32;
  p_align : int32
}

let parse_phdr elfbits =
  bitmatch elfbits with
    { p_type : 32 : littleendian;	(* Segment type.  *)
      p_offset : 32 : littleendian;	(* Segment file offset.  *)
      p_vaddr : 32 : littleendian;	(* Segment virtual address.  *)
      p_paddr : 32 : littleendian;	(* Segment physical address.  *)
      p_filesz : 32 : littleendian;	(* Segment size in file.  *)
      p_memsz : 32 : littleendian;	(* Segment size in memory.  *)
      p_flags : 32 : littleendian;	(* Segment flags.  *)
      p_align : 32 : littleendian } ->	(* Segment alignment.  *)
      { p_type = p_type;
        p_offset = p_offset;
	p_vaddr = p_vaddr;
	p_paddr = p_paddr;
	p_filesz = p_filesz;
	p_memsz = p_memsz;
	p_flags = p_flags;
	p_align = p_align }
  | { _ } ->
      raise (Elf_read_error "Can't parse phdr")

(*
let parse_dyn elfbits =
  bitmatch elfbits with
    { d_tag : 32 : littleendian;	(* Dynamic entry type.  *)
      d_val : 32 : littleendian } ->	(* Integer value (or address value).  *)
  | { _ } ->
      raise (Elf_read_error "Can't parse dyn")
*)

let bits n = Int32.mul 8l n

let extract_section elfbits shdr =
  Bitstring.subbitstring elfbits (Int32.to_int (bits shdr.sh_offset))
    (Int32.to_int (bits shdr.sh_size))

let get_string stringsec offset =
  let b = Buffer.create 10 in
  let rec gather bits =
    bitmatch bits with
      { "\000" : 8 : string } -> Buffer.contents b
    | { c : 8 : string } ->
        Buffer.add_string b c;
	gather (Bitstring.dropbits 8 bits) in
  gather (Bitstring.dropbits (offset * 8) stringsec)

let read_file filename =
  let elfbits = Bitstring.bitstring_of_file filename in
  let ehdr = parse_ehdr elfbits in
  Printf.printf "Number of program headers: %d\n" ehdr.e_phnum;
  Printf.printf "Program header offset: %ld\n" ehdr.e_phoff;
  Printf.printf "Number of section headers: %d\n" ehdr.e_shnum;
  Printf.printf "Section header offset: %ld\n" ehdr.e_shoff;
  elfbits, ehdr

let get_section_headers elfbits ehdr =
  Array.init ehdr.e_shnum
    (fun i ->
      let shdr_bits = Bitstring.subbitstring elfbits
        (8 * ((Int32.to_int ehdr.e_shoff) + i * ehdr.e_shentsize))
	(8 * ehdr.e_shentsize) in
      parse_shdr shdr_bits)

let get_program_headers elfbits ehdr =
  Array.init ehdr.e_phnum
    (fun i ->
      let phdr_bits = Bitstring.subbitstring elfbits
        (8 * ((Int32.to_int ehdr.e_phoff) + i * ehdr.e_phentsize))
	(8 * ehdr.e_phentsize) in
      parse_phdr phdr_bits)

let print_section_names elfbits ehdr shdr_arr =
  let sec_string_tab = extract_section elfbits shdr_arr.(ehdr.e_shstrndx) in
  for i = 0 to (Array.length shdr_arr - 1) do
    Printf.printf "Section %d: name '%s'\n" i
      (get_string sec_string_tab (Int32.to_int shdr_arr.(i).sh_name))
  done

let get_section_by_name elfbits ehdr shdr_arr name =
  let sec_string_tab = extract_section elfbits shdr_arr.(ehdr.e_shstrndx) in
  let found_sec = ArrayLabels.fold_left
    ~f:(fun found shdr ->
      match found with
        Some _ -> found
      | None ->
          let this_section_name =
	    get_string sec_string_tab (Int32.to_int shdr.sh_name) in
	  if this_section_name = name then Some shdr else found)
    ~init:None
    shdr_arr in
  match found_sec with
    None -> raise Not_found
  | Some shdr -> extract_section elfbits shdr
