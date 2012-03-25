module DR = Dwarfreader

type line_state_machine_state =
  {
    address : int;
    file : int;
    line: int;
    column : int;
    is_stmt : bool;
    basic_block : bool;
    end_sequence : bool;
    prologue_end : bool;
    epilogue_begin : bool;
    isa : int
  }

let new_state ~default_is_stmt =
  {
    address = 0;
    file = 1;
    line = 1;
    column = 0;
    is_stmt = default_is_stmt;
    basic_block = false;
    end_sequence = false;
    prologue_end = false;
    epilogue_begin = false;
    isa = 0
  }

type file_name =
  {
    filename : string;
    directory_index : int;
    last_modification : Big_int.big_int;
    file_length : int
  }

type line_prog_hdr =
  {
    unit_length : int32;
    version : int;
    header_length : int32;
    minimum_instruction_length : int;
    default_is_stmt : bool;
    line_base : int;
    line_range : int;
    opcode_base : int;
    standard_opcode_lengths : int array;
    include_directories : string array;
    file_names : file_name array
  }

let read_byte_vec dwbits num_items =
  let rec scan acc dwbits remaining_items =
    match remaining_items with
      0 -> (List.rev acc), dwbits
    | n ->
	bitmatch dwbits with
	  { item : 8 : littleendian;
	    rest : -1 : bitstring } ->
	      scan (item::acc) rest (pred remaining_items)
	| { _ } ->
	    raise (DR.Dwarf_parse_error "parse_line_number_prog_header") in
  scan [] dwbits num_items

let read_string_list dwbits =
  let rec scan acc dwbits =
    let str, rest = DR.get_string dwbits in
    match str with
      "" -> (List.rev acc), rest
    | n -> scan (n::acc) rest in
  scan [] dwbits

let read_filename_list dwbits =
  let rec scan acc dwbits =
    let filename, rest = DR.get_string dwbits in
    if filename = "" then
      (List.rev acc), rest
    else begin
      let dir_index, rest = DR.parse_uleb128_int rest in
      let mtime, rest = DR.parse_uleb128 rest in
      let filelen, rest = DR.parse_uleb128_int rest in
      let fname = { filename = filename;
        	    directory_index = dir_index;
		    last_modification = mtime;
		    file_length = filelen } in
      scan (fname::acc) rest
    end in
  scan [] dwbits

let parse_line_number_prog_header dwbits =
  bitmatch dwbits with
    { unit_length : 32 : littleendian;
      version : 16 : littleendian;
      header_length : 32 : littleendian;
      minimum_instruction_length : 8 : littleendian;
      default_is_stmt : 8 : littleendian;
      line_base : 8 : littleendian;
      line_range : 8 : littleendian;
      opcode_base : 8 : littleendian;
      rest : -1 : bitstring } ->
  let standard_opcode_lengths, dwbits = read_byte_vec rest (opcode_base - 1) in
  let include_directories, dwbits = read_string_list dwbits in
  let filename_list, dwbits = read_filename_list dwbits in
  { unit_length = unit_length;
    version = version;
    header_length = header_length;
    minimum_instruction_length = minimum_instruction_length;
    default_is_stmt = default_is_stmt <> 0;
    line_base = line_base;
    line_range = line_range;
    opcode_base = opcode_base;
    standard_opcode_lengths = Array.of_list standard_opcode_lengths;
    include_directories = Array.of_list include_directories;
    file_names = Array.of_list filename_list }, dwbits

let parse_lines dwbits =
  let hdr, dwbits' = parse_line_number_prog_header dwbits in
  hdr, dwbits'
