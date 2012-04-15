type 'code block =
  {
    (* Index of this node in a containing array.  *)
    mutable self_index : int;
    mutable code : 'code;
    id : string;
    mutable predecessors : 'code block list;
    mutable successors : 'code block list;
    mutable parent : 'code block option;
    mutable dfnum : int;
    (* An array of elements of this type can be indexed by a dfnum: in that
       case, VERTEX will be an indirect pointer to the real element.  *)
    mutable vertex : 'code block option;
    mutable ancestor : 'code block option;
    mutable semi : 'code block option;
    mutable idom : 'code block option;
    mutable idomchild : 'code block list;
    mutable samedom : 'code block option;
    mutable bucket : 'code block list;
    mutable domfront : 'code block list;
    mutable visited : bool;
    mutable live_in : Boolset.t;
    mutable live_out : Boolset.t
  }

let make_block idx id code =
  {
    self_index = idx;
    code = code;
    id = id;
    predecessors = [];
    successors = [];
    parent = None;
    dfnum = -1;
    vertex = None;
    ancestor = None;
    semi = None;
    idom = None;
    idomchild = [];
    samedom = None;
    bucket = [];
    domfront = [];
    visited = false;
    live_in = Boolset.empty;
    live_out = Boolset.empty
  }

