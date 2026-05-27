(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open ControlFlowGraph
open Apron

(* Signature for the variables *)

module type VARS = sig
  val support : var list
end

(*
  Signature of abstract domains representing sets of envrionments
  (for instance: a map from variable to their bounds).
 *)

module type DOMAIN = sig
  (* type of abstract elements *)
  (* an element of type t abstracts a set of mappings from variables
       to integers
     *)
  type t

  (* initial environment, with all variables initialized to 0 *)
  val init : t

  (* empty set of environments *)
  val bottom : t

  (* assign an integer expression to a variable *)
  val assign : t -> var -> int_expr -> t

  (* filter environments to keep only those satisfying the boolean expression *)
  val guard : t -> bool_expr -> t

  (* abstract join *)
  val join : t -> t -> t

  (* abstract meet *)
  val meet : t -> t -> t

  (* widening *)
  val widen : t -> t -> t

  (* narrowing *)
  val narrow : t -> t -> t

  (* whether an abstract element is included in another one *)
  val leq : t -> t -> bool

  (* whether the abstract element represents the empty set *)
  val is_bottom : t -> bool

  (* prints *)
  val pp : Format.formatter -> t -> unit
end

module Value_to_Domain (V : ValueDomain.VALUE_DOMAIN) (Vars : VARS): DOMAIN =
  struct
    module VMap = ControlFlowGraph.VarMap
    type t = V.t VMap.t
    
    let init : t = List.fold_left (fun map v -> VMap.add v (V.const Z.zero) map) VMap.empty Vars.support

    let bottom : t = VMap.empty

    let rec eval_int_expr env = function
    | CFG_int_unary (op,e) -> V.unary (eval_int_expr env e) op
    | CFG_int_binary (op,e1,e2) -> V.binary (eval_int_expr env e1) (eval_int_expr env e2) op
    | CFG_int_var v ->
       if VMap.mem v env then VMap.find v env else V.bottom
    | CFG_int_const n -> V.const n
    | CFG_int_rand (n1,n2) -> V.rand n1 n2

    let assign env v exp =
      if not (VMap.mem v env) then bottom
      else
        VMap.add v (eval_int_expr env exp) env

    type evaluated_tree =
    | ETVar of var
    | ETConst of Z.t
    | ETRand of Z.t * Z.t
    | ETBinop of AbstractSyntax.int_binary_op * (evaluated_tree * V.t) * (evaluated_tree * V.t)
    | ETUnop of AbstractSyntax.int_unary_op * (evaluated_tree * V.t)

    let pointwise_op f e1 e2 =
      VMap.union (fun _ v1 v2 -> Some (f v1 v2)) e1 e2

    let join = pointwise_op V.join

    let meet : t -> t -> t = pointwise_op V.meet

    let widen : t -> t -> t = pointwise_op V.widen

    let narrow : t -> t -> t = pointwise_op V.narrow

    let rec forward_evaluation env = function
    | CFG_int_unary (op,e) ->
      let (t,v) = forward_evaluation env e in
      (ETUnop (op,(t,v)),V.unary v op)
    | CFG_int_binary (op,e1,e2) ->
      let (t1,v1) = forward_evaluation env e1 in
      let (t2,v2) = forward_evaluation env e2 in
      (ETBinop (op,(t1,v1),(t2,v2)),V.binary v1 v2 op)
    | CFG_int_var v ->
      (ETVar v,if VMap.mem v env then VMap.find v env else V.bottom)
    | CFG_int_const n ->
      (ETConst n,V.const n)
    | CFG_int_rand (n1,n2) ->
      (ETRand (n1,n2),V.rand n1 n2)
    
    let rec backward_evaluation env v_bwd = function
    | ETVar v -> 
      if VMap.mem v env then VMap.add v v_bwd env else bottom
    | ETConst _ -> env
    | ETRand _ -> env
    | ETBinop (op,(t1,v1),(t2,v2)) -> 
      let (v1_bwd,v2_bwd) = V.bwd_binary v1 v2 op v_bwd in
      meet (backward_evaluation env v1_bwd t1) (backward_evaluation env v2_bwd t2)
    | ETUnop (op,(t,v)) ->
      let v_bwd = V.bwd_unary v op v_bwd in
      backward_evaluation env v_bwd t

    let guard env =
      let rec aux is_not = function
      | CFG_bool_unary (_,e) -> aux (not is_not) e
      | CFG_bool_binary (op,e1,e2) ->
        let env1 = aux is_not e1 in
        let env2 = aux is_not e2 in
        begin match op with
        | AbstractSyntax.AST_AND -> if is_not then join else meet
        | AbstractSyntax.AST_OR -> if is_not then meet else join 
        end env1 env2
      | CFG_bool_const b ->
        let b = if is_not then not b else b in
        if b then env else bottom
      | CFG_bool_rand -> env
      | CFG_compare (op,e1,e2) -> 
        let op = match op with
        | AbstractSyntax.AST_EQUAL -> if is_not then AbstractSyntax.AST_NOT_EQUAL else op
        | AbstractSyntax.AST_NOT_EQUAL -> if is_not then AbstractSyntax.AST_EQUAL else op
        | AbstractSyntax.AST_LESS -> if is_not then AbstractSyntax.AST_GREATER_EQUAL else op
        | AbstractSyntax.AST_GREATER_EQUAL -> if is_not then AbstractSyntax.AST_LESS else op
        | AbstractSyntax.AST_LESS_EQUAL -> if is_not then AbstractSyntax.AST_GREATER else op
        | AbstractSyntax.AST_GREATER -> if is_not then AbstractSyntax.AST_LESS_EQUAL else op
        in
        let (t1,v1) = forward_evaluation env e1 in
        let (t2,v2) = forward_evaluation env e2 in
        let (v1_bwd,v2_bwd) = V.compare v1 v2 op in
        let env1 = backward_evaluation env v1_bwd t1 in
        backward_evaluation env1 v2_bwd t2 
    in aux false

    let leq e1 e2 =
      VMap.fold (fun k v acc -> acc && VMap.mem k e2 && V.leq v (VMap.find k e2)) e2 true

    let is_bottom : t -> bool = VMap.is_empty

    let print_var fmt var =
      Format.fprintf fmt "{id = %d; name = %s}" var.var_id var.var_name
    
    let pp fmt vmap =
        VMap.iter (fun v s -> Format.fprintf fmt "%a -> %a@\n" print_var v V.pp s) vmap
  end


module SignDomain (V : VARS) : DOMAIN = struct
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

    type t = MSet.t
    let init = MSet.singleton (List.fold_left (fun map v -> VMap.add v Zero map) VMap.empty V.support)
    let bottom = MSet.empty
    let assign set var e = MSet.map (assign var e) set
    let guard set e = MSet.filter (fun map -> bool_sat_to_bool (satisfy_bool_expr map e)) set
    let join = MSet.union
    let meet = MSet.inter
    let widen = join
    let narrow = meet
    let is_bottom = MSet.is_empty
  end


module PolyhedraDomain (V:VARS) : DOMAIN = struct
  let env = Environment.make (Array.of_list (List.map (fun v -> Var.of_string v.var_name) V.support)) [||]
  type man = Polka.loose Polka.t
  let manager = Polka.manager_alloc_loose ()

  let rec expr_to_texpr = function
  | CFG_int_unary (unop,e) ->
    begin match unop with
    | AST_UNARY_PLUS -> expr_to_texpr e
    | AST_UNARY_MINUS -> Texpr1.Unop (Texpr1.Neg,expr_to_texpr e,Texpr1.Int,Texpr1.Near)
    end
  | CFG_int_binary (binop,e1,e2) ->
    Texpr1.Binop (
      begin match binop with
        | AST_PLUS -> Texpr1.Add
        | AST_MINUS -> Texpr1.Sub
        | AST_DIVIDE -> Texpr1.Div
        | AST_MODULO -> Texpr1.Mod
        | AST_MULTIPLY -> Texpr1.Mul 
      end,
      expr_to_texpr e1,
      expr_to_texpr e2,
      Texpr1.Int,
      Texpr1.Near)
  | CFG_int_var v ->
    Texpr1.Var (Var.of_string v.var_name)
  | CFG_int_const n ->
    Texpr1.Cst (Coeff.s_of_int (Z.to_int n))
  | CFG_int_rand (a,b) ->
    Texpr1.Cst (Coeff.i_of_int (Z.to_int a) (Z.to_int b))
    
  type t = man Abstract1.t

  let assign poly v e =
    Abstract1.assign_texpr manager poly (Var.of_string v.var_name) (Texpr1.of_expr env (expr_to_texpr e)) None

  let init : t = 
    let a = Abstract1.top manager env in
    List.fold_left (fun a v -> assign a v (CFG_int_const Z.zero)) a V.support

  let bottom : t = Abstract1.bottom manager env

  let join : t -> t -> t = Abstract1.join manager

  let meet : t -> t -> t = Abstract1.meet manager

  let rec guard poly bexpr =
    let rec aux is_not = function
    | CFG_bool_unary (_,e) -> aux (not is_not) e
    | CFG_bool_binary (op,e1,e2) ->
      let poly1 = aux is_not e1 in
      let poly2 = aux is_not e2 in
      begin match op with
      | AbstractSyntax.AST_AND -> if is_not then join else meet
      | AbstractSyntax.AST_OR -> if is_not then meet else join 
      end poly1 poly2
    | CFG_bool_const b ->
      let b = if is_not then not b else b in
      if b then poly else bottom
    | CFG_bool_rand -> poly
    | CFG_compare (op,e1,e2) ->
      let op = match op with
      | AbstractSyntax.AST_EQUAL -> if is_not then AbstractSyntax.AST_NOT_EQUAL else op
      | AbstractSyntax.AST_NOT_EQUAL -> if is_not then AbstractSyntax.AST_EQUAL else op
      | AbstractSyntax.AST_LESS -> if is_not then AbstractSyntax.AST_GREATER_EQUAL else op
      | AbstractSyntax.AST_GREATER_EQUAL -> if is_not then AbstractSyntax.AST_LESS else op
      | AbstractSyntax.AST_LESS_EQUAL -> if is_not then AbstractSyntax.AST_GREATER else op
      | AbstractSyntax.AST_GREATER -> if is_not then AbstractSyntax.AST_LESS_EQUAL else op
      in
      let t1 = expr_to_texpr e1 in
      let t2 = expr_to_texpr e2 in
      let t1_2 = Texpr1.Binop (Texpr1.Sub,t1,t2,Texpr1.Int,Texpr1.Near) in
      let texpr1_2 = Texpr1.of_expr env t1_2 in
      let t2_1 = Texpr1.Binop (Texpr1.Sub,t2,t1,Texpr1.Int,Texpr1.Near) in
      let texpr2_1 = Texpr1.of_expr env t2_1 in
      begin match op with
      | AbstractSyntax.AST_EQUAL -> 
        let c = Tcons1.make texpr1_2 Lincons0.EQ in
        let ar = Tcons1.array_make env 1 in
        Tcons1.array_set ar 0 c;
        Abstract1.meet_tcons_array manager poly ar
      | AbstractSyntax.AST_NOT_EQUAL ->
        let c1 = Tcons1.make texpr1_2 Lincons0.SUP in
        let ar1 = Tcons1.array_make env 1 in
        Tcons1.array_set ar1 0 c1;
        let poly1 = Abstract1.meet_tcons_array manager poly ar1 in
        let c2 = Tcons1.make texpr2_1 Lincons0.SUP in
        let ar2 = Tcons1.array_make env 1 in
        Tcons1.array_set ar2 0 c2;
        let poly2 = Abstract1.meet_tcons_array manager poly ar2 in
        join poly1 poly2
      | AbstractSyntax.AST_LESS ->
        let c = Tcons1.make texpr2_1 Lincons0.SUP in
        let ar = Tcons1.array_make env 1 in
        Tcons1.array_set ar 0 c;
        Abstract1.meet_tcons_array manager poly ar
      | AbstractSyntax.AST_LESS_EQUAL ->
        let c = Tcons1.make texpr2_1 Lincons0.SUPEQ in
        let ar = Tcons1.array_make env 1 in
        Tcons1.array_set ar 0 c;
        Abstract1.meet_tcons_array manager poly ar
      | AbstractSyntax.AST_GREATER ->
        let c = Tcons1.make texpr1_2 Lincons0.SUP in
        let ar = Tcons1.array_make env 1 in
        Tcons1.array_set ar 0 c;
        Abstract1.meet_tcons_array manager poly ar
      | AbstractSyntax.AST_GREATER_EQUAL ->
        let c = Tcons1.make texpr1_2 Lincons0.SUPEQ in
        let ar = Tcons1.array_make env 1 in
        Tcons1.array_set ar 0 c;
        Abstract1.meet_tcons_array manager poly ar
      end
    in aux false bexpr

  let widen : t -> t -> t = Abstract1.widening manager

  let narrow : t -> t -> t = meet

  let leq : t -> t -> bool = Abstract1.is_leq manager

  let is_bottom : t -> bool = Abstract1.is_bottom manager

  let pp : Format.formatter -> t -> unit = Abstract1.print
end