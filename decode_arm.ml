open Insn

exception Bad_condition_code of int

let cond_of_code = function
    0b0000 -> Some Eq
  | 0b0001 -> Some Ne
  | 0b0010 -> Some Cs
  | 0b0011 -> Some Cc
  | 0b0100 -> Some Mi
  | 0b0101 -> Some Pl
  | 0b0110 -> Some Vs
  | 0b0111 -> Some Vc
  | 0b1000 -> Some Hi
  | 0b1001 -> Some Ls
  | 0b1010 -> Some Ge
  | 0b1011 -> Some Lt
  | 0b1100 -> Some Gt
  | 0b1101 -> Some Le
  | 0b1110 -> None
  | x -> raise (Bad_condition_code x)

let bad_insn =
  {
    opcode = BAD;
    write_operands = [| |];
    read_operands = [| |];
    write_flags = [];
    read_flags = [];
    clobber_flags = []
  }

let conditionalise cond opcode =
  match cond with
    None -> opcode
  | Some cond -> Conditional (cond, opcode)

let hard_reg n = Hard_reg n

(* Decode 28 remaining bits of NV space.  *)
let decode_nv_space ibits =
  bad_insn

let decode_movw cond ibits =
  bad_insn

let decode_movt cond ibits =
  bad_insn

let decode_msr_and_hints cond op1 rest =
  bad_insn

let decode_misc cond op1 bits19_8 op2 bits3_0 =
  bad_insn

let decode_halfword_mul_mac cond op1 bints19_8 op2 bits3_0 =
  bad_insn

(* op1 is bits 24-20 inclusive.  *)
let decode_mul_mac cond op1 bits19_8 bits3_0 =
  bitmatch Bitstring.dropbits 1 op1 with
    { 0b000 : 3; s_bit : 1 } ->
      let rd, rm =
        (bitmatch bits19_8 with { rd : 4; _ : 4; rm : 4 } -> rd, rm)
      and rn = (bitmatch bits3_0 with { rn : 4 } -> rn) in
      {
        opcode = conditionalise cond Mul;
	write_operands = [| hard_reg rd |];
	read_operands = [| hard_reg rn; hard_reg rm |];
	read_flags = [];
	write_flags = if s_bit then [N; Z] else [];
	clobber_flags = []
      }
  | { 0b001 : 3; s_bit : 1 } ->
      let rd, ra, rm =
        (bitmatch bits19_8 with { rd : 4; ra : 4; rm : 4 } -> rd, ra, rm)
      and rn = (bitmatch bits3_0 with { rn : 4 } -> rn) in
      {
        opcode = conditionalise cond Mla;
	write_operands = [| hard_reg rd |];
	read_operands = [| hard_reg rn; hard_reg rm; hard_reg ra |];
	read_flags = [];
	write_flags = if s_bit then [N; Z] else [];
	clobber_flags = []
      }
  | { 0b0100 : 4 } ->
      let rdhi, rdlo, rm =
        (bitmatch bits19_8 with { rdhi : 4; rdlo : 4; rm : 4 } ->
	  rdhi, rdlo, rm)
      and rn = (bitmatch bits3_0 with { rn : 4 } -> rn) in
      {
        opcode = conditionalise cond Umaal;
	write_operands = [| hard_reg rdlo; hard_reg rdhi |];
	read_operands = [| hard_reg rdlo; hard_reg rdhi; hard_reg rn;
			   hard_reg rm |];
	read_flags = []; write_flags = []; clobber_flags = []
      }
  | { 0b0101 : 4 } -> bad_insn
  | { 0b0110 : 4 } ->
      let rd, ra, rm =
        (bitmatch bits19_8 with { rd : 4; ra : 4; rm : 4 } -> rd, ra, rm)
      and rn = (bitmatch bits3_0 with { rn : 4 } -> rn) in
      {
        opcode = conditionalise cond Mls;
	write_operands = [| hard_reg rd |];
	read_operands = [| hard_reg rn; hard_reg rm; hard_reg ra |];
	read_flags = []; write_flags = []; clobber_flags = []
      }
  | { 0b0111 : 4 } -> bad_insn
  | { true : 1; signed : 1; false : 1; s_bit : 1 } ->
      let rdhi, rdlo, rm =
        (bitmatch bits19_8 with { rdhi : 4; rdlo : 4; rm : 4 } ->
	  rdhi, rdlo, rm)
      and rn = (bitmatch bits3_0 with { rn : 4 } -> rn) in
      let opc = if signed then Smull else Umull in
      {
        opcode = conditionalise cond opc;
	write_operands = [| hard_reg rdlo; hard_reg rdhi |];
	read_operands = [| hard_reg rn; hard_reg rm |];
	read_flags = [];
	write_flags = if s_bit then [N; Z] else [];
	clobber_flags = []
      }
  | { true : 1; signed : 1; true : 1; s_bit : 1 } ->
      let rdhi, rdlo, rm =
        (bitmatch bits19_8 with { rdhi : 4; rdlo : 4; rm : 4 } ->
	  rdhi, rdlo, rm)
      and rn = (bitmatch bits3_0 with { rn : 4 } -> rn) in
      let opc = if signed then Smlal else Umlal in
      {
        opcode = conditionalise cond opc;
	write_operands = [| hard_reg rdlo; hard_reg rdhi |];
	read_operands = [| hard_reg rdlo; hard_reg rdhi; hard_reg rn;
			   hard_reg rm |];
	read_flags = [];
	write_flags = if s_bit then [N; Z] else [];
	clobber_flags = []
      }
  | { _ } -> bad_insn

let decode_sync cond op1 bits19_8 bits3_0 =
  bad_insn

let decode_extra_ld_st ~unpriv cond op1 bits19_8 bits3_0 =
  bad_insn

let union_flags a b =
  a @ b

let add_flag_if_sbit flags new_flag s_bit =
  if s_bit && not (List.mem new_flag flags)
     && not (new_flag = C_from_shift && (List.mem C flags)) then
    new_flag :: flags
  else
    flags

(* Transform opcode by adding a shift around it.  Also note any flags read or
   written by the shifter.  *)
let decode_imm_shift opcode s_bit shiftbits rd_operands ~rd_flags ~wr_flags =
  bitmatch shiftbits with
    { imm : 5; 0b00 : 2 } ->
      if imm = 0 then
        opcode, rd_operands, rd_flags, wr_flags
      else
        Shifted (opcode, Lsl),
	Array.append rd_operands [| Immediate (Int32.of_int imm) |],
	rd_flags, add_flag_if_sbit wr_flags C_from_shift s_bit
  | { imm : 5; 0b01 : 2 } ->
      let imm' = if imm = 0 then 32 else imm in
      Shifted (opcode, Lsr),
      Array.append rd_operands [| Immediate (Int32.of_int imm') |],
      rd_flags, add_flag_if_sbit wr_flags C_from_shift s_bit
  | { imm : 5; 0b10 : 2 } ->
      let imm' = if imm = 0 then 32 else imm in
      Shifted (opcode, Asr),
      Array.append rd_operands [| Immediate (Int32.of_int imm') |],
      rd_flags, add_flag_if_sbit wr_flags C_from_shift s_bit
  | { 0 : 5; 0b11 : 2 } ->
      Shifted (opcode, Rrx),
      rd_operands,
      union_flags rd_flags [C], add_flag_if_sbit wr_flags C_from_shift s_bit
  | { imm : 5; 0b11 : 2 } ->
      Shifted (opcode, Ror),
      Array.append rd_operands [| Immediate (Int32.of_int imm) |],
      rd_flags, add_flag_if_sbit wr_flags C_from_shift s_bit

let decode_imm_shift_for_mem shiftbits =
  bitmatch shiftbits with
    { imm : 5; 0b00 : 2 } ->
      if imm = 0 then
        None, [| |]
      else
	Some Lsl, [| Immediate (Int32.of_int imm) |]
  | { imm : 5; 0b01 : 2 } ->
    let imm' = if imm = 0 then 32 else imm in
    Some Lsr, [| Immediate (Int32.of_int imm') |]
  | { imm : 5; 0b10 : 2 } ->
    let imm' = if imm = 0 then 32 else imm in
    Some Asr, [| Immediate (Int32.of_int imm') |]
  | { 0 : 5; 0b11 : 2 } ->
    Some Rrx, [| |]
  | { imm : 5; 0b11 : 2 } ->
    Some Ror, [| Immediate (Int32.of_int imm) |]

let imm32_rotate i amt =
  let amt' = amt land 31 in
  match amt' with
    0 -> i
  | n -> Int32.logor (Int32.shift_right_logical i amt')
		     (Int32.shift_left i (32 - amt'))

let immed_carry_effect s_bit rotation modified_imm wr_flags =
  if s_bit && (rotation <> 0) && not (List.mem C wr_flags) then
    if (Int32.logand modified_imm 0x80000000l) <> 0l then
      C_one :: wr_flags
    else
      C_zero :: wr_flags
  else
    wr_flags

let decode_imm_const s_bit coded_imm rd_operands ~wr_flags =
  bitmatch coded_imm with
    { rotation : 4 : bind (rotation * 2); immed : 8 } ->
    let int_val = imm32_rotate (Int32.of_int immed) rotation in
    let wr_flags' = immed_carry_effect s_bit rotation int_val wr_flags in
    Array.append rd_operands [| Immediate int_val |], wr_flags'

(* The set of flags written depends on the opcode.  *)
let conditional_set_flags_for_op opcode s_bit =
  if not s_bit then
    []
  else match opcode with
      And
    | Eor
    | Orr
    | Mov
    | Bic
    | Mvn
    | Tst
    | Teq -> [N; Z]
    | Sub
    | Rsb
    | Add
    | Adc
    | Sbc
    | Rsc
    | Cmp
    | Cmn -> [C; V; N; Z]
    | _ -> []

(* Some operations always read the flags register.  *)
let read_flags_for_op opcode =
  match opcode with
    Adc | Sbc | Rsc -> [C]
  | _ -> []

let decode_dp cond opcode ~s_bit ~reg bits19_0 =
  if reg then
    bitmatch bits19_0 with
      { rn : 4; rd : 4; imm_shift : 7 : bitstring; false : 1; rm : 4 } ->
	let rd_operands =
	  match opcode with
	    Mov | Mvn -> [| hard_reg rm |]
	  | _ -> [| hard_reg rn; hard_reg rm |]
	and rd_flags = read_flags_for_op opcode
	and wr_flags = conditional_set_flags_for_op opcode s_bit in
	let wr_operands =
	  match opcode with
	    Cmp | Cmn | Teq | Tst -> [| |]
	  | _ -> [| hard_reg rd |] in
	let opcode', rd_operands', rd_flags', wr_flags'
	  = decode_imm_shift opcode s_bit imm_shift rd_operands ~rd_flags
			     ~wr_flags in
	{
	  opcode = conditionalise cond opcode';
	  read_operands = rd_operands';
	  write_operands = wr_operands;
	  read_flags = rd_flags';
	  write_flags = wr_flags';
	  clobber_flags = []
	}
    | { _ } -> bad_insn
  else
    bitmatch bits19_0 with
      { rn : 4; rd : 4; coded_imm : 12 : bitstring } ->
      let rd_operands =
        match opcode with
	  Mov | Mvn -> [| |]
	| _ -> [| hard_reg rn |]
      and rd_flags = read_flags_for_op opcode
      and wr_flags = conditional_set_flags_for_op opcode s_bit in
      let wr_operands =
        match opcode with
          Cmp | Cmn | Teq | Tst -> [| |]
	| _ -> [| hard_reg rd |] in
      let rd_operands', wr_flags'
        = decode_imm_const s_bit coded_imm rd_operands ~wr_flags in
      {
        opcode = conditionalise cond opcode;
	read_operands = rd_operands';
	write_operands = wr_operands;
	read_flags = rd_flags;
	write_flags = wr_flags';
	clobber_flags = []
      }

let decode_dp_reg_or_imm cond bits24_0 ~reg =
  bitmatch bits24_0 with
    { 0b0000 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond And ~s_bit ~reg bits19_0
  | { 0b0001 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Eor ~s_bit ~reg bits19_0
  | { 0b0010 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Sub ~s_bit ~reg bits19_0
  | { 0b0011 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Rsb ~s_bit ~reg bits19_0
  | { 0b0100 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Add ~s_bit ~reg bits19_0
  | { 0b0101 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Adc ~s_bit ~reg bits19_0
  | { 0b0110 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Sbc ~s_bit ~reg bits19_0
  | { 0b0111 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Rsc ~s_bit ~reg bits19_0
  | { 0b10001 : 5; bits19_0 : 20 : bitstring } ->
      decode_dp cond Tst ~s_bit:true ~reg bits19_0
  | { 0b10011 : 5; bits19_0 : 20 : bitstring } ->
      decode_dp cond Teq ~s_bit:true ~reg bits19_0
  | { 0b10101 : 5; bits19_0 : 20 : bitstring } ->
      decode_dp cond Cmp ~s_bit:true ~reg bits19_0
  | { 0b10111 : 5; bits19_0 : 20 : bitstring } ->
      decode_dp cond Cmn ~s_bit:true ~reg bits19_0
  | { 0b1100 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Orr ~s_bit ~reg bits19_0
  | { 0b1101 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Mov ~s_bit ~reg bits19_0
  | { 0b1110 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Bic ~s_bit ~reg bits19_0
  | { 0b1111 : 4; s_bit : 1; bits19_0 : 20 : bitstring } ->
      decode_dp cond Mvn ~s_bit ~reg bits19_0
  | { _ } -> bad_insn

let decode_dp_reg_shifted_reg cond op1 bits19_8 op2 bits3_0 =
  bad_insn

(* Decode 32 bits of data-processing & media instructions.  *)
let decode_dp_misc cond ibits =
  bitmatch ibits with
    { _ : 4;
      0b001 : 3;
      op1 : 5 : bitstring;
      rest : 20 : bitstring } ->
        (bitmatch op1 with
	  { 0b10000 : 5 } -> decode_movw cond rest
	| { 0b10100 : 5 } -> decode_movt cond rest
	| { (0b10010 | 0b10110) : 5 } ->
	  decode_msr_and_hints cond op1 rest
	| { _ } ->
	  let bits24_0 = Bitstring.subbitstring ibits 7 25 in
	  decode_dp_reg_or_imm cond bits24_0 ~reg:false)
  | { _ : 4;
      0b000 : 3;
      op1 : 5 : bitstring;
      bits19_8 : 12 : bitstring;
      op2 : 4 : bitstring;
      bits3_0 : 4 : bitstring } ->
        let bits24_0 = Bitstring.subbitstring ibits 7 25 in
        (bitmatch Bitstring.concat [op1; op2] with
	  { 0b10 : 2; _ : 2; false : 1;
	    false : 1; _ : 3 } ->
	    decode_misc cond op1 bits19_8 op2 bits3_0
	| { 0b10 : 2; _ : 2; false : 1;
	    true : 1; _ : 2; false : 1 } ->
	    decode_halfword_mul_mac cond op1 bits19_8 op2 bits3_0
        | { false : 1; _ : 4;
	    0b1001 : 4 } -> decode_mul_mac cond op1 bits19_8 bits3_0
	| { true : 1; _ : 4;
	    0b1001 : 4 } -> decode_sync cond op1 bits19_8 bits3_0
	| { false : 1; _ : 2; true : 1; _ : 1;
	    (0b1011 | 0b1101 | 0b1111) : 4 } ->
	    decode_extra_ld_st ~unpriv:true cond op1 bits19_8 bits3_0
	| { _ : 5;
	    (0b1011 | 0b1101 | 0b1111) : 4 } ->
	    decode_extra_ld_st ~unpriv:false cond op1 bits19_8 bits3_0
	| { _ : 5;
	    _ : 3; false : 1 } -> decode_dp_reg_or_imm cond bits24_0 ~reg:true
	| { _ : 5;
	    false : 1; _ : 2; true : 1 } ->
	    decode_dp_reg_shifted_reg cond op1 bits19_8 op2 bits3_0)

let sign_extend imm32 bitpos =
  let bit = Int32.shift_left 1l bitpos in
  let ones = Int32.lognot (Int32.pred bit) in
  if Int32.logand imm32 bit = 0l then imm32 else (Int32.logor imm32 ones)

let decode_mem ?(unprivileged=false) ?(byte=false) ~load ~reg cond bits25_0 =
  if unprivileged then
    bad_insn
  else
    if reg then
      bitmatch bits25_0 with
	{ _ : 1; p : 1; u : 1; _ : 1; w : 1; _ : 1; rn : 4; rt : 4;
	  shift_bits : 7 : bitstring; false : 1; rm : 4 } ->
	  let writeback = (not p) || w in
	  let wr_operands =
	    match load, writeback with
	      false, true -> [| hard_reg rn |]
	    | false, false -> [| |]
	    | true, true -> [| hard_reg rt; hard_reg rn |]
	    | true, false -> [| hard_reg rt |] in
	  let rd_operands =
	    if load then [| hard_reg rn; hard_reg rm |]
	    else [| hard_reg rt; hard_reg rn; hard_reg rm |] in
	  let shift_opt, shift_operands = decode_imm_shift_for_mem shift_bits in
	  let am = match shift_opt, u with
	    None, true -> Base_plus_reg
	  | None, false -> Base_minus_reg
	  | Some shift, true -> Base_plus_shifted_reg shift
	  | Some shift, false -> Base_minus_shifted_reg shift in
	  let ai = { addr_mode = am; writeback = writeback; pre_modify = p } in
	  let opc =
	    match load, byte with
	      false, true -> Strb ai
	    | false, false -> Str ai
	    | true, true -> Ldrb ai
	    | true, false -> Ldr ai in
	  {
	    opcode = conditionalise cond opc;
	    write_operands = wr_operands;
	    read_operands = Array.append rd_operands shift_operands;
	    write_flags = []; read_flags = []; clobber_flags = []
	  }
      | { _ } -> bad_insn
    else  (* base+offset addressing *)
      bitmatch bits25_0 with
        { false : 1; p : 1; u : 1; _ : 1; w : 1; _ : 1; rn : 4; rt : 4;
	  imm : 12 } ->
	  let writeback = (not p) || w in
	  let wr_operands =
	    match load, writeback with
	      false, true -> [| hard_reg rn |]
	    | false, false -> [| |]
	    | true, true -> [| hard_reg rt; hard_reg rn |]
	    | true, false -> [| hard_reg rt |] in
	  let simm = sign_extend (Int32.of_int imm) 11 in
	  let immval =
	    if u then Immediate simm
	    else Immediate (Int32.neg simm) in
	  let rd_operands =
	    if load then [| hard_reg rn; immval |]
	    else [| hard_reg rt; hard_reg rn; immval |] in
	  let ai = { addr_mode = Base_plus_imm; writeback = writeback;
		     pre_modify = p } in
	  let opc =
	    match load, byte with 
	      false, true -> Strb ai
	    | false, false -> Str ai
	    | true, true -> Ldrb ai
	    | true, false -> Ldr ai in
	  {
	    opcode = conditionalise cond opc;
	    write_operands = wr_operands;
	    read_operands = rd_operands;
	    write_flags = []; read_flags = []; clobber_flags = []
	  }
      | { _ } -> bad_insn

let decode_str ?(unprivileged=false) ~reg cond bits25_0 =
  decode_mem ~unprivileged ~byte:false ~load:false ~reg cond bits25_0

let decode_ldr ?(unprivileged=false) ?(literal=false) ~reg cond
	       bits25_0 =
  decode_mem ~unprivileged ~byte:false ~load:true ~reg cond bits25_0

let decode_strb ?(unprivileged=false) ~reg cond bits25_0 =
  decode_mem ~unprivileged ~byte:true ~load:false ~reg cond bits25_0

let decode_ldrb ?(unprivileged=false) ?(literal=false) ~reg cond bits25_0 =
  decode_mem ~unprivileged ~byte:true ~load:true ~reg cond bits25_0

(* Decode 32 bits of ibits.  *)
let decode_ldr_str_ldrb_strb cond ibits =
  let bits25_0 = Bitstring.subbitstring ibits 6 26 in
  bitmatch (Bitstring.subbitstring ibits 4 28) with
    { 0b010 : 3; (0b00010 | 0b01010) : 5 } ->
    decode_str ~unprivileged:true ~reg:false cond bits25_0
  | { 0b011 : 3; (0b00010 | 0b01010) : 5; _ : 15; false : 1 } ->
    decode_str ~unprivileged:true ~reg:true cond bits25_0
  | { 0b010 : 3; _ : 2; false : 1; _ : 1; false : 1 } ->
    decode_str ~reg:false cond bits25_0
  | { 0b011 : 3; _ : 2; false : 1; _ : 1; false : 1; _ : 15; false : 1 } ->
    decode_str ~reg:true cond bits25_0
  | { 0b010 : 3; (0b00011 | 0b01011) : 5 } ->
    decode_ldr ~unprivileged:true ~reg:false cond bits25_0
  | { 0b011 : 3; (0b00011 | 0b01011) : 5; _ : 15; false : 1 } ->
    decode_ldr ~unprivileged:true ~reg:true cond bits25_0
  | { 0b010 : 3; _ : 2; false : 1; _ : 1; true : 1; 0b1111 : 4 } ->
    decode_ldr ~literal:true ~reg:false cond bits25_0
  | { 0b010 : 3; _ : 2; false : 1; _ : 1; true : 1 } ->
    decode_ldr ~reg:false cond bits25_0
  | { 0b011 : 3; _ : 2; false : 1; _ : 1; true : 1; _ : 15; false : 1 } ->
    decode_ldr ~reg:true cond bits25_0
  | { 0b010 : 3; (0b00110 | 0b01110) : 5 } ->
    decode_strb ~unprivileged:true ~reg:false cond bits25_0
  | { 0b011 : 3; (0b00110 | 0b01110) : 5; _ : 15; false : 1 } ->
    decode_strb ~unprivileged:true ~reg:true cond bits25_0
  | { 0b010 : 3; _ : 2; true : 1; _ : 1; false : 1 } ->
    decode_strb ~reg:false cond bits25_0
  | { 0b011 : 3; _ : 2; true : 1; _ : 1; false : 1; _ : 15; false : 1 } ->
    decode_strb ~reg:true cond bits25_0
  | { 0b010 : 3; (0b00111 | 0b01111) : 5 } ->
    decode_ldrb ~unprivileged:true ~reg:false cond bits25_0
  | { 0b011 : 3; (0b00111 | 0b01111) : 5; _ : 15; false : 1 } ->
    decode_ldrb ~unprivileged:true ~reg:true cond bits25_0
  | { 0b010 : 3; _ : 2; true : 1; _ : 1; true : 1; 0b1111 : 4 } ->
    decode_ldrb ~literal:true ~reg:false cond bits25_0
  | { 0b010 : 3; _ : 2; true : 1; _ : 1; true : 1 } ->
    decode_ldrb ~reg:false cond bits25_0
  | { 0b011 : 3; _ : 2; true : 1; _ : 1; true : 1; _ : 15; false : 1 } ->
    decode_ldrb ~reg:true cond bits25_0
  | { _ } -> bad_insn

let decode_media cond ibits =
  bad_insn

let decode_branch cond ~link bits23_0 =
  bitmatch bits23_0 with
    { bits : 24 } ->
      let offset = sign_extend (Int32.of_int bits) 23 in
      let opcode = if link then Bl else B in
        {
	  opcode = conditionalise cond opcode;
	  write_operands = [| |];
	  read_operands = [| PC_relative offset |];
	  write_flags = []; read_flags = []; clobber_flags = []
	}
  | { _ } -> bad_insn

let hard_reg_list bits =
  let rlist = ref [] in
  for i = 15 downto 0 do
    if bits land (1 lsl i) <> 0 then
      rlist := (hard_reg i) :: !rlist
  done;
  Array.of_list !rlist

let decode_stm cond bits24_0 =
  bitmatch bits24_0 with
    { before : 1; increment : 1; false : 1; writeback : 1; false : 1;
      basereg : 4; reglist : 16 } ->
      let info = { before = before; increment = increment } in
      let wr_operands = if writeback then [| hard_reg basereg |] else [| |] in
      let regs = hard_reg_list reglist in
      {
        opcode = conditionalise cond (Stm info);
	read_operands = Array.append [| hard_reg basereg |] regs;
	write_operands = wr_operands;
	write_flags = []; read_flags = []; clobber_flags = []
      }
  | { _ } -> bad_insn

let decode_ldm cond ~exception_return bits24_0 =
  bitmatch bits24_0 with
    { before : 1; increment : 1; false : 1; writeback : 1; true : 1;
      basereg : 4; reglist : 16 } ->
      let info = { before = before; increment = increment } in
      let wr_operands = if writeback then [| hard_reg basereg |] else [| |] in
      let regs = hard_reg_list reglist in
      {
        opcode = conditionalise cond (Stm info);
	read_operands = [| hard_reg basereg |];
	write_operands = Array.append wr_operands regs;
	write_flags = []; read_flags = []; clobber_flags = []
      }
  | { _ } -> bad_insn

(* Decode 32 bits of ibits.  *)
let decode_branch_block_xfer cond ibits =
  bitmatch ibits with
    { _ : 4; 0b1011 : 4; bits23_0 : 24 : bitstring } ->
      decode_branch cond ~link:true bits23_0
  | { _ : 4; 0b1010 : 4; bits23_0 : 24 : bitstring } ->
      decode_branch cond ~link:false bits23_0
  | { _ : 4; 0b100 : 3; _ : 4; false : 1 } ->
      let bits24_0 = Bitstring.subbitstring ibits 7 25 in
      decode_stm cond bits24_0
  | { _ : 4; 0b100 : 3; _ : 4; true : 1 } ->
      let bits24_0 = Bitstring.subbitstring ibits 7 25
      and exception_return = Bitstring.is_set ibits 16 in
      decode_ldm cond ~exception_return bits24_0

let decode_svc_copro cond ibits =
  bad_insn

let decode_insn ibits =
  bitmatch ibits with
    { 0b1111 : 4; rest : 28 : bitstring } ->
      decode_nv_space rest
  | { cond : 4; (0b000 | 0b001) : 3 } ->
      decode_dp_misc (cond_of_code cond) ibits
  | { cond : 4; 0b010 : 3 } ->
      decode_ldr_str_ldrb_strb (cond_of_code cond) ibits
  | { cond : 4; 0b011 : 3; _ : 20; false : 1 } ->
      decode_ldr_str_ldrb_strb (cond_of_code cond) ibits
  | { cond : 4; 0b011 : 3; _ : 20; true : 1 } ->
      decode_media (cond_of_code cond) ibits
  | { cond : 4; (0b100 | 0b101) : 3 } ->
      decode_branch_block_xfer (cond_of_code cond) ibits
  | { cond : 4; (0b110 | 0b111) : 3 } ->
      decode_svc_copro (cond_of_code cond) ibits
  | { _ } ->
      bad_insn
  
let decode_insns ibits num_insns =
  let rec scan acc ibits insns_left =
    if insns_left = 0 then
      (List.rev acc), ibits
    else
      bitmatch ibits with
        { b0 : 8 : bitstring;
	  b1 : 8 : bitstring;
	  b2 : 8 : bitstring;
	  b3 : 8 : bitstring;
	  rest : -1 : bitstring } ->
	  let insn = Bitstring.concat [b3; b2; b1; b0] in
          let decoded_insn = decode_insn insn in
	  scan (decoded_insn :: acc) rest (pred insns_left)
      | { bad : -1 : bitstring } -> scan acc bad 0 in
  scan [] ibits num_insns

let decode_immediate imm_insn =
  let insn_bits = BITSTRING { imm_insn : 32 } in
  decode_insn insn_bits
