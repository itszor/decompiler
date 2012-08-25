module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

let choose_name (name, idx) =
  match name with
    CT.Hard_reg n -> Printf.sprintf "r%d_%d" n idx
  | CT.VFP_sreg r -> Printf.sprintf "s%d_%d" r idx
  | CT.VFP_dreg r -> Printf.sprintf "s%d_%d" r idx
  | CT.Stack s ->
      if s < 0 then
        Printf.sprintf "local%d_%d" (-s) idx
      else
        Printf.sprintf "incoming%d_%d" s idx
  | CT.Temp t -> Printf.sprintf "tmp%d_%d" t idx
  | CT.Status _ -> Printf.sprintf "status_%d" idx (* Fixme! *)
  | CT.Stack_var nm -> Printf.sprintf "%s_%d" nm idx

type possible_type =
    Known of Ctype.ctype
  | Strong of Ctype.ctype
  | Weak of Ctype.ctype

let choose_better a b =
  a (* ? *)

let reduce_typelist tlist =
  let rec reduce = function
    [] -> raise Not_found
  | [(Known ct | Strong ct | Weak ct as x)] -> x
  | Known a :: (Strong b | Weak b) :: rest -> reduce (Known a :: rest)
  | (Strong a | Weak a) :: Known b :: rest -> reduce (Known b :: rest)
  | Strong a :: Weak b :: rest -> reduce (Strong a :: rest)
  | Weak a :: Strong b :: rest -> reduce (Strong b :: rest)
  | (Known _ as a) :: (Known _ as b) :: rest
  | (Strong _ as a) :: (Strong _ as b) :: rest
  | (Weak _ as a) :: (Weak _ as b) :: rest ->
      reduce (choose_better a b :: rest) in
  match reduce tlist with
    Known x | Strong x | Weak x -> x

let choose_type ct_for_cu ssaname inforec =
  try
    let infos = Hashtbl.find inforec.Typedb.infotag ssaname in
    let possible_types =
      List.fold_right
	(fun info ptypes ->
	  match info with
	    Typedb.Used_as_addr access ->
	      begin match access with
	        Irtypes.U8 ->
		  Weak (Ctype.C_pointer Ctype.C_char) :: ptypes
	      | Irtypes.S8 ->
		  Weak (Ctype.C_pointer (Ctype.C_signed Ctype.C_char))
		    :: ptypes
	      | Irtypes.U16 ->
	          Weak (Ctype.C_pointer (Ctype.C_unsigned Ctype.C_short))
		    :: ptypes
	      | Irtypes.S16 ->
		  Weak (Ctype.C_pointer Ctype.C_short) :: ptypes
	      | Irtypes.Word ->
	          Weak (Ctype.C_pointer Ctype.C_int)
		    :: Weak (Ctype.C_pointer (Ctype.C_unsigned Ctype.C_int))
		    :: Weak (Ctype.C_pointer (Ctype.C_pointer Ctype.C_void))
		    :: ptypes
	      | Irtypes.Dword ->
	          Weak (Ctype.C_pointer Ctype.C_longlong)
		    :: Weak (Ctype.C_pointer
			      (Ctype.C_unsigned Ctype.C_longlong))
		    :: ptypes
	      end
	  | Typedb.Loaded_pc_rel -> ptypes
	  | Typedb.Type_known ct -> Known ct :: ptypes
	  | Typedb.Used_as_type ct -> Strong ct :: ptypes
	  | Typedb.Byte_loads ->
	      Weak Ctype.C_char :: ptypes
	  | Typedb.Signed_byte_loads ->
	      Weak (Ctype.C_signed Ctype.C_char) :: ptypes
	  | Typedb.Byte_stores ->
	      Weak Ctype.C_char :: Weak (Ctype.C_signed Ctype.C_char) :: ptypes
	  | Typedb.Halfword_loads ->
	      Weak (Ctype.C_unsigned Ctype.C_short) :: ptypes
	  | Typedb.Signed_halfword_loads ->
	      Weak Ctype.C_short :: ptypes
	  | Typedb.Halfword_stores ->
	      Weak Ctype.C_short :: Weak (Ctype.C_unsigned Ctype.C_short)
	        :: ptypes
	  | Typedb.Word_loads
	  | Typedb.Word_stores ->
	      Weak Ctype.C_int :: Weak (Ctype.C_unsigned Ctype.C_int) :: ptypes
	  | Typedb.Doubleword_loads
	  | Typedb.Doubleword_stores ->
	      Weak Ctype.C_longlong
	        :: Weak (Ctype.C_unsigned Ctype.C_longlong) :: ptypes
          | Typedb.Code_pointer ->
	      Weak (Ctype.C_pointer Ctype.C_void) :: ptypes)
	infos
	[] in
    reduce_typelist possible_types
  with Not_found ->
    (* Some kind of fallback...  *)
    if Typedb.probably_pointer ct_for_cu ssaname inforec then
      Ctype.C_pointer Ctype.C_void
    else
      Ctype.C_int

let choose_vartypes blk_arr ct_for_cu inforec =
  let ht = Hashtbl.create 10 in
  let defs = Defs.get_defs blk_arr in
  Hashtbl.iter
    (fun ssaname definfo ->
      if definfo.Defs.num_uses > 0 then
	let name = choose_name ssaname
	and typ = choose_type ct_for_cu ssaname inforec in
	Log.printf 3 "decl: %s %s\n" (Ctype.string_of_ctype typ) name;
	Hashtbl.add ht ssaname (name, typ))
    defs;
  ht
