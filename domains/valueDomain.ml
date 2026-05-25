(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Signature of abstract domains representing sets of integers
  (for instance: constants or intervals).
 *)

open Frontend
open AbstractSyntax

module type VALUE_DOMAIN = sig
  (* type of abstract elements *)
  (* an element of type t abstracts a set of integers *)
  type t

  (* unrestricted value: [-oo,+oo] *)
  val top : t

  (* bottom value: empty set *)
  val bottom : t

  (* constant: {c} *)
  val const : Z.t -> t

  (* interval: [a,b] *)
  val rand : Z.t -> Z.t -> t

  (* unary operation *)
  val unary : t -> int_unary_op -> t

  (* binary operation *)
  val binary : t -> t -> int_binary_op -> t

  (* comparison *)
  (* [compare x y op] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is true for some v' in y
       - y' abstracts the set of v' in y such that v op v' is true for some v  in x
       i.e., we filter the abstract values x and y knowing that the test is true

       a safe, but not precise implementation, would be:
       compare x y op = (x,y)
     *)
  val compare : t -> t -> compare_op -> t * t

  (* backards unary operation *)
  (* [bwd_unary x op r] return x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x
     *)
  val bwd_unary : t -> int_unary_op -> t -> t

  (* backward binary operation *)
  (* [bwd_binary x y op r] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
       - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
       i.e., we filter the abstract values x and y knowing that, after
       applying the operation op, the result is in r
      *)
  val bwd_binary : t -> t -> int_binary_op -> t -> t * t

  (* set-theoretic operations *)
  val join : t -> t -> t

  val meet : t -> t -> t

  (* widening *)
  val widen : t -> t -> t

  (* narrowing *)
  val narrow : t -> t -> t

  (* subset inclusion of concretizations *)
  val leq : t -> t -> bool

  (* check the emptiness of the concretization *)
  val is_bottom : t -> bool

  (* print abstract element *)
  val pp : Format.formatter -> t -> unit
end


type interval_border =
  | PlusInf
  | MinusInf
  | Value of Z.t

type interval = 
    Interval of interval_border * interval_border
  | Empty

let interval_eq int1 int2 =
  match int1,int2 with
  | Empty, Empty -> true
  | Interval (a1,b1), Interval (a2,b2) -> a1 = a2 && b1 = b2
  | _ -> false

let border_min a b =
  match a,b with
  | MinusInf,_ | _,MinusInf -> MinusInf
  | Value v1,Value v2 -> Value (min v1 v2)
  | Value v,_| _,Value v -> Value v
  | _ -> PlusInf

let border_max a b = 
  match a,b with
  | PlusInf,_ | _,PlusInf -> PlusInf
  | Value v1,Value v2 -> Value (max v1 v2)
  | Value v,_ | _,Value v -> Value v
  | _ -> MinusInf

let border_ge a b =
  a = border_max a b

let border_gt a b =
  match a,b with
  | PlusInf,_ | _,MinusInf -> true
  | _,PlusInf | MinusInf,_ -> false
  | Value n,Value n' -> Z.gt n n'

let conv_if_empty = function
  | Empty -> Empty
  | Interval (a,b) as int -> 
    begin match a,b with
    | PlusInf,_ | _,MinusInf -> Empty
    | Value n1, Value n2 -> if Z.gt n1 n2 then Empty else int
    | _ -> int
    end

let interval_intersect int1 int2 =
  match int1,int2 with
  | Empty,_ | _,Empty -> Empty
  | Interval (a,b), Interval (a',b') -> conv_if_empty (Interval (border_max a a',border_min b b'))

let uminus = function
  | PlusInf -> MinusInf
  | MinusInf -> PlusInf
  | Value v -> Value (Z.sub Z.zero v)

let border_add a b = 
  match a,b with
  | PlusInf, PlusInf | PlusInf, Value _ | Value _, PlusInf -> PlusInf
  | MinusInf, MinusInf | MinusInf, Value _ | Value _, MinusInf -> MinusInf
  | Value v1, Value v2 -> Value (Z.add v1 v2)
  | _ -> failwith "Undefined"

let border_sub a b =
  border_add a (uminus b)

let interval_add int1 int2 =
  match int1,int2 with
  | Empty, _ | _, Empty -> Empty
  | Interval (a1,b1), Interval (a2,b2) ->
    Interval (border_add a1 a2, border_add b1 b2)

let interval_sub int1 int2 =
  match int1,int2 with
  | Empty, _ | _, Empty -> Empty
  | Interval (a1,b1), Interval (a2,b2) ->
    Interval (border_sub a1 b2, border_sub b1 a2)

let border_mul a b =
  match a,b with
  | PlusInf, MinusInf | MinusInf, PlusInf -> MinusInf
  | PlusInf, PlusInf | MinusInf, MinusInf -> PlusInf
  | Value v1, Value v2 -> Value (Z.mul v1 v2)
  | Value v, inf | inf, Value v ->
    if v = Z.zero then Value Z.zero
    else if Z.lt v Z.zero then inf
    else uminus inf

let border_min_list l = 
  List.fold_left (fun m n -> border_min m n) PlusInf l

let border_max_list l = 
  List.fold_left (fun m n -> border_max m n) MinusInf l

let interval_mul int1 int2 =
  match int1,int2 with
  | Empty, _ | _, Empty -> Empty
  | Interval (a1,b1), Interval (a2,b2) ->
    let cross_products = [border_mul a1 a2; border_mul a1 b2; border_mul b1 a2; border_mul b1 b2] in
    Interval (border_min_list cross_products,border_max_list cross_products)

let border_abs =
  function
  | Value n -> Value (Z.abs n)
  | _ -> PlusInf

let is_positive = function
  | Value n -> Z.geq n Z.zero
  | PlusInf -> true
  | MinusInf -> false

let is_negative = function
  | Value n -> Z.leq n Z.zero
  | PlusInf -> false
  | MinusInf -> true

let abstract_union int1 int2 =
  match int1,int2 with
  | Empty, i | i, Empty -> i
  | Interval (a1,b1), Interval (a2,b2) ->
    Interval (border_min a1 a2, border_max b1 b2)

let get_pos_neg = function
  | Empty -> Empty,Empty
  | Interval (a,b) ->
    ( if is_positive a then Interval (a,b) else Interval (Value Z.zero,b)),
    (if is_negative b then Interval (a,b) else Interval (a,Value Z.zero))

let interval_pos_mod int m =
  match int with
  | Empty -> Empty
  | Interval (a,b) -> 
    if border_gt m b then
        Interval (a,b)
      else
        Interval ((Value Z.zero),(border_sub m (Value Z.one)))

let interval_mod int1 int2 = 
  match int1,int2 with
  | Empty,_ | _,Empty -> Empty
  | _, Interval (a',b') ->
    if is_negative a' && is_positive b' then
      Empty
    else
      let max' = border_max (border_abs a') (border_abs b') in
      let int_pos,int_neg = get_pos_neg int1 in
      let int1' = interval_pos_mod int_pos max' in
      let int2' = interval_pos_mod (interval_sub (Interval (Value Z.zero,Value Z.zero)) int_neg) max' in
      abstract_union int1' (interval_sub (Interval (Value Z.zero,Value Z.zero)) int2')

let interval_div int1 int2 = 
  match int1,int2 with
  | Empty,_ | _,Empty -> Empty
  | Interval (a,b), Interval (a',b') -> 
    if is_negative a' && is_positive b' then
      Empty
    else
      failwith "TODO"

let widening int1 int2 =
  match int1,int2 with
  | Empty, i | i, Empty -> i
  | Interval (a1,b1), Interval (a2,b2) ->
    if border_ge a2 a1 && border_ge b1 b2 then int1
    else Interval ((if a1 <> a2 then MinusInf else a1), if b1 <> b2 then PlusInf else b1)

let const n =
  Interval (Value n, Value n)

let unary int = function
  | AbstractSyntax.AST_UNARY_PLUS -> int
  | AbstractSyntax.AST_UNARY_MINUS -> interval_sub (const Z.zero) int

let binary int1 int2 = function
  | AbstractSyntax.AST_PLUS -> interval_add int1 int2
  | AbstractSyntax.AST_MINUS -> interval_sub int1 int2
  | AbstractSyntax.AST_MULTIPLY -> interval_mul int1 int2
  | AbstractSyntax.AST_MODULO -> interval_mod int1 int2
  | AbstractSyntax.AST_DIVIDE -> interval_div int1 int2

let compare x y op =
  match x,y with
  | Empty,_ | _,Empty -> Empty,Empty
  | Interval (a,b), Interval (a',b') ->
    begin match op with
    | AbstractSyntax.AST_EQUAL -> let int = interval_intersect x y in int,int
    | AbstractSyntax.AST_NOT_EQUAL -> 
      let int2 = 
        if a = b then (
          if a = a' then
            conv_if_empty (Interval (border_add a' (Value Z.one),b'))
          else if a = b' then
            conv_if_empty (Interval (a',border_sub b' (Value Z.one)))
          else 
            y
        ) else y
      in let int1 =
        if a' = b' then (
          if a' = a then
            conv_if_empty (Interval (border_add a (Value Z.one),b))
          else if a' = b then
            conv_if_empty (Interval (a,border_sub b (Value Z.one)))
          else 
            x
        ) else x
      in int1,int2
    | AbstractSyntax.AST_LESS -> interval_intersect x (Interval (MinusInf, border_sub b' (Value Z.one))), interval_intersect (Interval (border_add a (Value Z.one),PlusInf)) y
    | AbstractSyntax.AST_LESS_EQUAL -> interval_intersect x (Interval (MinusInf, b')), interval_intersect (Interval (a,PlusInf)) y
    | AbstractSyntax.AST_GREATER -> interval_intersect x (Interval (border_add a' (Value Z.one),PlusInf)), interval_intersect (Interval (MinusInf, border_sub b (Value Z.one))) y
    | AbstractSyntax.AST_GREATER_EQUAL -> interval_intersect x (Interval (a',PlusInf)), interval_intersect (Interval (MinusInf, b)) y
    end

let bwd_unary x op r =
  interval_intersect x (unary r op)
  
let bwd_binary x y op r =
  match op with
  | AbstractSyntax.AST_PLUS -> interval_intersect x (interval_sub r y), interval_intersect y (interval_sub r x)
  | AbstractSyntax.AST_MINUS -> interval_intersect x (interval_add r y), interval_intersect y (interval_sub x r)
  | AbstractSyntax.AST_MULTIPLY -> interval_intersect x (interval_div r y), interval_intersect y (interval_div r x)
  | AbstractSyntax.AST_DIVIDE -> x,y
  | AbstractSyntax.AST_MODULO -> x,y

let narrow x y = failwith "TODO"

let leq x y =
  x = interval_intersect x y

let is_bottom x =
  x = Empty

let pp fmt = function
  | Empty -> Format.fprintf fmt "[Empty]"
  | Interval (a,b) ->
    let s1 = match a with
      | PlusInf -> "PlusInf"
      | MinusInf -> "MinusInf"
      | Value n -> Z.to_string n
    in let s2 = match b with
      | PlusInf -> "PlusInf"
      | MinusInf -> "MinusInf"
      | Value n -> Z.to_string n
    in Format.fprintf fmt "[%s ; %s]" s1 s2

module IntervalDomain =
  (struct
    type t = interval
    let top = Interval (MinusInf,PlusInf)
    let bottom = Empty
    let const = const
    let rand a b = 
      if Z.leq a b then Interval (Value a, Value b)
      else Empty
    let unary = unary
    let binary = binary
    let compare = compare
    let bwd_unary = bwd_unary
    let bwd_binary = bwd_binary
    let join = abstract_union
    let meet = interval_intersect
    let narrow = narrow
    let widen = widening
    let leq = leq
    let is_bottom = is_bottom
    let pp = pp
  end: VALUE_DOMAIN)