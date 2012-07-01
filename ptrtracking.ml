open Defs

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

exception Untrackable

(* Given a use of an SSA variable USE (typically a pointer), return a list of
   (def, offset) pairs. Raise Untrackable if it cannot be done.  *)

let track_pointer defs use =
  let rec track use offset =
    try
      let dinf = Hashtbl.find defs use in
      match dinf.src with
	C.SSAReg (d, dn) -> (dinf.src, offset) :: track (d, dn) offset
      | C.Binary (Irtypes.Add, (C.SSAReg (d, dn) as reg), C.Immed imm) ->
          let offset' = Int32.add offset imm in
	  (reg, offset') :: track (d, dn) offset'
      | C.Binary (Irtypes.Sub, (C.SSAReg (d, dn) as reg), C.Immed imm) ->
          let offset' = Int32.sub offset imm in
	  (reg, offset') :: track (d, dn) offset'
      | C.Nullary Irtypes.Caller_saved
      | C.Nullary Irtypes.Special
      | C.Nullary Irtypes.Arg_in
      | C.Entity CT.Arg_out
      | C.Phi _
      | C.Load _
      | C.Immed _ -> [dinf.src, offset]
      | _ ->
	  Log.printf 3 "Can't track: %s\n" (C.string_of_code dinf.src);
	  raise Untrackable
    with Not_found ->
      Log.printf 3 "Can't find def for %s\n"
	(C.string_of_code (C.SSAReg (fst use, snd use)));
      raise Untrackable in
  track use 0l
