type reg = Hard_reg of int
         | Float_reg of int

type binop = Add
           | Sub

type extop = Fnargs

type mem = Addr of int32

type expr

type _ code =
    Reg : reg -> reg code
  | SSAReg : reg * int -> reg code
  | Set : reg code * 'a code -> unit code
  | Immed : int32 -> expr code
  | Binop : binop * 'a code * 'b code -> expr code
  | Load : mem * 'a code -> expr code
  | Store : mem * 'a code * 'b code -> unit code
  | Phi : node array -> expr code

and node = Reg_code of reg code
         | Expr_code of expr code
