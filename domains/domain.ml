(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open ControlFlowGraph

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

module Value_to_Domain (V : ValueDomain.VALUE_DOMAIN) : DOMAIN =
  struct
    module VMap = ControlFlowGraph.VarMap
    type t = 
      | Bottom
      | Env of V.t VMap.t
    
    let init : t = Env VMap.empty

    let bottom : t = Bottom

    let rec eval_int_expr env = function
    | CFG_int_unary (op,e) -> V.unary (eval_int_expr env e) op
    | CFG_int_binary (op,e1,e2) -> V.binary (eval_int_expr env e1) (eval_int_expr env e2) op
    | CFG_int_var v ->
       if VMap.mem v env then VMap.find v env else V.bottom
    | CFG_int_const n -> V.const n
    | CFG_int_rand (n1,n2) -> V.rand n1 n2

    let assign env v exp =
      match env with
      | Bottom -> Bottom
      | Env env -> Env (VMap.add v (eval_int_expr env exp) env)

    let guard : t -> bool_expr -> t = failwith "TODO"

    let pointwise_op f t1 t2 = match t1,t2 with
    | Bottom,t | t,Bottom -> t
    | Env e1,Env e2 ->
      Env (VMap.union (fun _ v1 v2 -> Some (f v1 v2)) e1 e2)

    let join = pointwise_op V.join

    let meet : t -> t -> t = pointwise_op V.meet

    let widen : t -> t -> t = pointwise_op V.widen

    let narrow : t -> t -> t = pointwise_op V.narrow

    let leq t1 t2 = match t1,t2 with
    | Bottom,_ -> true
    | _,Bottom -> false
    | Env e1,Env e2 ->
      VMap.fold (fun k v acc -> acc && VMap.mem k e2 && V.leq v (VMap.find k e2)) e2 true

    let is_bottom : t -> bool = function
      | Bottom -> true
      | _ -> false

    let print_var fmt var =
      Format.fprintf fmt "{id = %d; name = %s}" var.var_id var.var_name
    
    let pp fmt vmap =
      match vmap with
      | Env vmap ->
        VMap.iter (fun v s -> Format.fprintf fmt "%a -> %a@\n" print_var v V.pp s) vmap
      | Bottom -> Format.fprintf fmt "Bottom"
  end