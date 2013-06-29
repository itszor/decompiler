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
	        CT.U8 ->
		  Weak (Ctype.C_pointer Ctype.C_char) :: ptypes
	      | CT.S8 ->
		  Weak (Ctype.C_pointer (Ctype.C_signed Ctype.C_char))
		    :: ptypes
	      | CT.U16 ->
	          Weak (Ctype.C_pointer (Ctype.C_unsigned Ctype.C_short))
		    :: ptypes
	      | CT.S16 ->
		  Weak (Ctype.C_pointer Ctype.C_short) :: ptypes
	      | CT.Word ->
	          Weak (Ctype.C_pointer Ctype.C_int)
		    :: Weak (Ctype.C_pointer (Ctype.C_unsigned Ctype.C_int))
		    :: Weak (Ctype.C_pointer (Ctype.C_pointer Ctype.C_void))
		    :: ptypes
	      | CT.Dword ->
	          Weak (Ctype.C_pointer Ctype.C_longlong)
		    :: Weak (Ctype.C_pointer
			      (Ctype.C_unsigned Ctype.C_longlong))
		    :: ptypes
	      end
	  | Typedb.Loaded_pc_rel -> ptypes
	  | Typedb.Type_known ct -> Known ct :: ptypes
	  | Typedb.Known_ptr_type_offset (ct, o) ->
	      if o = 0l then
	        Known ct :: ptypes
	      else
	        ptypes (* FIXME! *)
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

type reg_or_ssareg =
    T_ssareg of (CT.reg * int)
  | T_reg of CT.reg

type vartype_info =
  {
    vt_name : string;
    vt_type : Ctype.ctype;
    mutable vt_needs_prototype : bool
  }

let choose_vartypes blk_arr ct_for_cu inforec =
  let ht = Hashtbl.create 10 in
  let defs = Defs.get_defs blk_arr in
  Hashtbl.iter
    (fun ssaname definfo ->
      if definfo.Defs.num_uses > 0 then
	let name = choose_name ssaname
	and typ = choose_type ct_for_cu ssaname inforec in
	Log.printf 3 "decl: %s %s\n" (Ctype.string_of_ctype typ) name;
	Hashtbl.add ht (T_ssareg ssaname)
	  { vt_name = name; vt_type = typ; vt_needs_prototype = true })
    defs;
  ht

let base_offset addr =
  match addr with
    C.SSAReg id -> Some (id, 0l)
  | C.Binary (CT.Add, C.SSAReg id, C.Immed o) -> Some (id, o)
  | C.Binary (CT.Sub, C.SSAReg id, C.Immed o) -> Some (id, Int32.neg o)
  | _ -> None

(* Later on in decompilation (FIXME: or earlier too?) we can build a table of
   ltypes representing SSA registers.  Returns a BatMultiMap from ssa id
   (reg, num) to one or more ltype data.
   This file probably isn't the best place to put this!  *)

let create_ltype_map blk_arr inforec ct_for_cu =
  let open Ltype in
  let defs = Defs.get_defs blk_arr in
  Array.iter
    (fun blk -> CS.iter
      (fun stmt ->
        ignore (C.map
	  (fun node ->
	    match node with
	      C.Set (C.SSAReg dstid,
		     C.Unary (CT.Address_of,
			      C.Binary (CT.Raw_offset vt, _,
					C.Immed offset))) ->
		(* We also need to "decay" the type by adding types
		   corresponding to e.g. each level of a struct which could be
		   represented by the same offset.  *)
		let rec peel typ offs acc =
		  match Ctype.peel_aggregate typ offs ct_for_cu with
		    None -> (typ, offs) :: acc
		  | Some (subtyp, suboff) ->
		      (typ, offs) :: peel subtyp suboff acc in
		let peeled = peel vt (Int32.to_int offset) [] in
		begin match peeled with
		  [] -> ()
		| [vt', offset'] ->
		    Typedb.record_ltype inforec dstid
		      (Ptrto_offset (Ctype vt', Int32.of_int offset'));
		| several ->
		    let types =
		      List.map
			(fun (typ, offs) ->
			  Ptrto_offset (Ctype typ, Int32.of_int offs))
			several in
		    Typedb.record_ltype inforec dstid (Alternatives types)
		end;
		C.Protect node
	    | C.Set (C.SSAReg dstid, C.Load (accsz, addr)) ->
	        begin match base_offset addr with
		  Some (base, off) ->
		    Typedb.record_ltype inforec dstid
		      (Deref_offset (Type_of base, off));
		    Typedb.record_ltype inforec dstid (Scalar accsz)
		| None -> ()
		end;
		C.Protect node
	    | C.Store (accsz, addr, C.SSAReg srcid) ->
	        begin match base_offset addr with
		  Some (base, off) ->
		    Typedb.record_ltype inforec srcid
		      (Deref_offset (Type_of base, off));
		    Typedb.record_ltype inforec srcid (Scalar accsz)
		| None -> ()
		end;
		C.Protect node
	    | _ -> node)
	  stmt))
      blk.Block.code)
    blk_arr

let dump_ltype_map inforec =
  BatMultiMap.iter
    (fun ((r, rn) as id) set ->
      Log.printf 3 "SSA id: %s\n" (Typedb.string_of_ssa_reg r rn);
      BatSet.iter
        (fun lt -> Log.printf 3 "  %s\n" (Ltype.string_of_ltype lt))
	set)
    inforec.Typedb.ltypemap

(*let solve_ltype_map inforec =
  let open Ltype in
  BatMultiMap.iter
    (fun id set ->
      BatSet.iter
        (fun lt ->
	  match lt with
	    Alternatives ltlist ->)
	set)
    inforec.Typedb.ltypemap*)
