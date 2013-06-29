(* A "low level" type representation, suitable for assigning to SSA registers
   prior to some unification phase (TBD!).  The level of information we have
   about each SSA reg may vary: some we know real C types for, others we only
   know what low-level operations are done on that reg.  The representation in
   this file tries to capture that.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

type ltype =
    Ctype of Ctype.ctype
  | Ctype_compat of Ctype.ctype
  | Pointer_to of ltype
    (* OFFSET bytes after a pointer to LTYPE.  *)
  | Ptrto_offset of ltype * int32
  | Dereference of ltype
    (* Type of object pointed to by LTYPE + offset.  *)
  | Deref_offset of ltype * int32
  | Scalar of CT.mem
  | Type_of of (CT.reg * int)
  | Alternatives of ltype list

let rec string_of_ltype = function
    Ctype ct -> Ctype.string_of_ctype ct
  | Ctype_compat ct -> Printf.sprintf "compat(%s)" (Ctype.string_of_ctype ct)
  | Pointer_to lt -> Printf.sprintf "ptr_to(%s)" (string_of_ltype lt)
  | Ptrto_offset (lt, o) ->
      Printf.sprintf "ptrto_off(%s, %ld)" (string_of_ltype lt) o
  | Dereference lt -> Printf.sprintf "deref(%s)" (string_of_ltype lt)
  | Deref_offset (lt, o) ->
      Printf.sprintf "deref_off(%s, %ld)" (string_of_ltype lt) o
  | Scalar m -> Printf.sprintf "scalar(%s)" (CT.string_of_mem m)
  | Type_of (r, rn) -> Printf.sprintf "type_of(%s_%d)" (CT.string_of_reg r) rn
  | Alternatives alt -> String.concat " or " (List.map string_of_ltype alt)

let rec ltypes_unify ltmap ctypes_for_cu type_a type_b =
  match type_a, type_b with
    Ctype ta, Ctype tb ->
      let ta' = Ctype.rem_typedefs_cv_quals ctypes_for_cu ta
      and tb' = Ctype.rem_typedefs_cv_quals ctypes_for_cu tb in
      (* This is a rather simplistic view of type equality in C...  *)
      ta' = tb'
  | Ctype (Ctype.C_pointer ta), Pointer_to (Ctype tb)
  | Ctype (Ctype.C_pointer ta), Ptrto_offset (Ctype tb, 0l) ->
      ltypes_unify ltmap ctypes_for_cu (Ctype ta) (Ctype tb)
  | Pointer_to (Ctype ta), Ctype (Ctype.C_pointer tb)
  | Ptrto_offset (Ctype ta, 0l), Ctype (Ctype.C_pointer tb) ->
      ltypes_unify ltmap ctypes_for_cu (Ctype ta) (Ctype tb)
  | Ctype ta, Dereference tb -> check_deref ctypes_for_cu ta tb 0l
  | Ctype ta, Deref_offset (tb, off) -> check_deref ctypes_for_cu ta tb off
  | Dereference ta, Ctype tb -> check_deref ctypes_for_cu tb ta 0l
  | Deref_offset (ta, off), Ctype tb -> check_deref ctypes_for_cu tb ta off

and check_deref ctypes_for_cu ct drt offs =
  true

type typescheme = Typevar of int
        	| Phystype of ltype

let ltype_solve ltmap ctypes_for_cu =
  let ht = Hashtbl.create 10 in
  ignore (BatMultiMap.foldi
    (fun id _ num -> Hashtbl.add ht id (Typevar num); succ num)
    ltmap
    0);
  
