let mkstring cl =
  let mystr = String.make (List.length cl) '\000' in
  for i = 0 to List.length cl - 1 do
    mystr.[i] <- List.nth cl i;
  done;
  mystr

let get_bs oflist =
  Bitstring.bitstring_of_string (mkstring (List.map Char.chr oflist))

let get_val oflist =
  let res, _ = Dwarfreader.parse_sleb128 (get_bs oflist) in
  Big_int.string_of_big_int res
