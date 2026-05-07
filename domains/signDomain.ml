open Frontend

type sign =
  | Zero
  | Plus
  | Minus
  | Top
  | Bot

module VMap = ControlFlowGraph.VarMap

let incl m1 m2 =
  VMap.fold (fun v s acc -> acc && VMap.mem v m2 && VMap.find v m2 = s) m1 true

module OrderedVMap =
  struct
    type t = sign VMap.t
    let compare m1 m2 = 
      let b1 = incl m1 m2 in
      let b2 = incl m2 m1 in
      if b1 && b2 then 0
      else if b1 then -1
      else 1
  end

module MSet = Set.Make(OrderedVMap)

let int_to_sign n =
  if Z.equal n Z.zero then Zero
  else if Z.lt Z.zero n then Plus
  else Minus

let binary_op_sign op s1 s2 =
  match op with
  | AbstractSyntax.AST_PLUS -> 
    begin match s1,s2 with
    | Plus,Plus | Plus,Zero | Zero,Plus -> Plus
    | Minus,Minus | Minus,Zero | Zero,Minus -> Minus
    | Zero,Zero -> Zero
    | Bot,_ | _,Bot -> Bot
    | _ -> Top
    end
  | AbstractSyntax.AST_MINUS ->
    begin match s1,s2 with
    | Plus,Minus | Plus,Zero | Zero,Minus -> Plus
    | Minus,Plus | Minus,Zero | Zero,Plus -> Minus
    | Zero,Zero -> Zero
    | Bot,_ | _,Bot -> Bot
    | _ -> Top
    end
  | AbstractSyntax.AST_MULTIPLY ->
    begin match s1,s2 with
    | Plus,Plus | Minus,Minus -> Plus
    | Plus,Minus | Minus,Plus -> Minus
    | Bot,_ | _,Bot -> Bot
    | Zero,_ | _,Zero -> Zero
    | _ -> Top
    end
  | AbstractSyntax.AST_DIVIDE ->
    begin match s1,s2 with
    | Plus,Plus | Minus,Minus -> Plus
    | Plus,Minus | Minus,Plus -> Minus
    | Bot,_ | _,Bot | _,Zero -> Bot
    | Zero,_ -> Zero
    | _ -> Top
    end
  | AbstractSyntax.AST_MODULO -> 
    begin match s1,s2 with
    | Bot,_ | _,Bot |_,Zero -> Bot
    | Zero,_ -> Zero
    | _ -> Top
    end

let unary_op_sign op s =
  match op with
  | AbstractSyntax.AST_UNARY_PLUS -> s
  | AbstractSyntax.AST_UNARY_MINUS ->
    begin match s with
    | Plus -> Minus
    | Minus -> Plus
    | _ -> s
    end

let rec eval_int_expr m =
    function 
    | ControlFlowGraph.CFG_int_const n ->
      int_to_sign n
    | ControlFlowGraph.CFG_int_rand (a,b) ->
      let sa = int_to_sign a in
      let sb = int_to_sign b in
      if sa = sb then sa
      else Top
    | ControlFlowGraph.CFG_int_var v -> 
        if VMap.mem v m then VMap.find v m
        else Bot
    | ControlFlowGraph.CFG_int_binary (op,e1,e2) ->
      binary_op_sign op (eval_int_expr m e1) (eval_int_expr m e2)
    | ControlFlowGraph.CFG_int_unary (op,e) ->
      unary_op_sign op (eval_int_expr m e)


type bool_sat =
  | Value of bool
  | False_Or_True

let unary_op_bool op b =
  match op with
  | AbstractSyntax.AST_NOT ->
    begin match b with
    | Value b -> Value (not b)
    | False_Or_True -> False_Or_True
    end

let binary_op_bool op b1 b2 =
  match op with
  | AbstractSyntax.AST_AND ->
    begin match b1,b2 with
    | Value false,_ | _,Value false -> Value false
    | False_Or_True,_ | _,False_Or_True -> False_Or_True
    | _ -> Value true
    end
  | AbstractSyntax.AST_OR ->
    begin match b1,b2 with
    | Value true,_ | _,Value true-> Value true
    | False_Or_True,_ | _,False_Or_True -> False_Or_True
    | _ -> Value false
    end

let bool_sat_to_bool = function
  | Value b -> b
  | _ -> true

let comp_sign op s1 s2 =
  match op with
  | AbstractSyntax.AST_GREATER_EQUAL ->
    begin match s1,s2 with
    | Bot,_ | _,Bot -> Value false
    | Plus,_ | _,Minus | Top,_ | _,Top -> Value true
    | Zero,Zero -> Value true
    | _ -> Value false
    end
  | AbstractSyntax.AST_GREATER ->
    begin match s1,s2 with
    | Bot,_ | _,Bot -> Value false
    | Plus,_ | _,Minus | Top,_ | _,Top -> Value true
    | _ -> Value false
    end
  | AbstractSyntax.AST_LESS_EQUAL ->
    begin match s1,s2 with
    | Bot,_ | _,Bot -> Value false
    | Minus,_ | _,Plus | Top,_ | _,Top -> Value true
    | Zero,Zero -> Value true
    | _ -> Value false
    end
  | AbstractSyntax.AST_LESS ->
    begin match s1,s2 with
    | Bot,_ | _,Bot -> Value false
    | Minus,_ | _,Plus | Top,_ | _,Top -> Value true
    | _ -> Value false
    end
  | AbstractSyntax.AST_EQUAL ->
    begin match s1,s2 with
    | Bot,_ | _,Bot -> Value false
    | Minus,Minus | Plus,Plus | Top,_ | _,Top -> Value true
    | Zero,Zero -> Value true
    | _ -> Value false
    end
  | AbstractSyntax.AST_NOT_EQUAL ->
    begin match s1,s2 with
    | Bot,_ | _,Bot -> Value false
    | Zero,Zero -> Value false
    | _ -> Value true
    end

  
let rec satisfy_bool_expr m = function
  | ControlFlowGraph.CFG_bool_unary (op,e) -> unary_op_bool op (satisfy_bool_expr m e)
  | ControlFlowGraph.CFG_bool_binary (op,e1,e2) -> binary_op_bool op (satisfy_bool_expr m e1) (satisfy_bool_expr m e2)
  | ControlFlowGraph.CFG_bool_const b -> Value b
  | ControlFlowGraph.CFG_bool_rand -> False_Or_True
  | ControlFlowGraph.CFG_compare (op,e1,e2) -> comp_sign op (eval_int_expr m e1) (eval_int_expr m e2)
  

let assign v e m = 
    let s = eval_int_expr m e in
    VMap.add v s m

let leq s1 s2 =
  let inter = MSet.inter s1 s2 in
  MSet.equal inter s1

let print_sign fmt =
  function
  | Plus -> Format.fprintf fmt "Plus"
  | Minus -> Format.fprintf fmt "Minus"
  | Zero -> Format.fprintf fmt "0"
  | Top -> Format.fprintf fmt "Top"
  | Bot -> Format.fprintf fmt "Bottom"

let print_var fmt var =
  Format.fprintf fmt "{id = %d; name = %s}" var.ControlFlowGraph.var_id var.ControlFlowGraph.var_name

let print_vmap fmt map =
  VMap.iter (fun v s -> Format.fprintf fmt "%a -> %a@\n" print_var v print_sign s) map

let pp fmt s =
  MSet.iter (fun m -> Format.fprintf fmt "{%a}@\n" print_vmap m) s

module SignDomain =
  struct
    type t = MSet.t
    let init = MSet.singleton VMap.empty
    let bottom = MSet.empty
    let assign set var e = MSet.map (assign var e) set
    let guard set e = MSet.filter (fun map -> bool_sat_to_bool (satisfy_bool_expr map e)) set
    let join = MSet.union
    let meet = MSet.inter
    let widen = join
    let narrow = meet
    let leq = leq
    let is_bottom = MSet.is_empty
    let pp = pp
  end