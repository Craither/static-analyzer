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
  
module SignDomain =
  (struct
    type t =
    | Zero
    | Plus
    | Minus
    | Top
    | Bot

    let top = Top

    let bottom = Bot

    let const n =
      if Z.equal n Z.zero then Zero
      else if Z.gt n Z.zero then Plus
      else Minus

    let rand n1 n2 =
      if Z.equal n1 Z.zero && Z.equal n2 Z.zero then Zero
      else if Z.gt n1 Z.zero && Z.gt n2 Z.zero then Plus
      else if Z.lt n1 Z.zero && Z.lt n2 Z.zero then Minus
      else Top

    let unary s = function
    | AbstractSyntax.AST_UNARY_PLUS -> s
    | AbstractSyntax.AST_UNARY_MINUS ->
      begin match s with
      | Plus -> Minus
      | Minus -> Plus
      | _ -> s
      end

    let binary s1 s2 = function
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
     
    let join s1 s2 =
      if s1 = bottom then s2
      else if s2 = bottom then s1
      else if s1 = s2 then s1
      else if s1 == Zero then s2
      else if s2 == Zero then s1
      else top
    
    let widen = join

    let meet s1 s2 =
      if s1 = top then s2
      else if s2 = top then s1
      else if s1 = s2 then s1
      else bottom
    
    let narrow = meet

    let compare s1 s2 = function
    | AbstractSyntax.AST_EQUAL -> let s = meet s1 s2 in  s,s
    | AbstractSyntax.AST_NOT_EQUAL ->
      begin match s1,s2 with
      | Bot,_ | _,Bot -> Bot,Bot
      | Zero,Zero -> Bot,Bot
      | _ -> s1,s2 end
    | AbstractSyntax.AST_GREATER -> 
      begin match s1,s2 with
      | Bot,_ | _,Bot -> Bot,Bot
      | Zero,Zero -> Bot,Bot
      | Zero,Plus -> Bot,Bot
      | Zero,Top -> Zero,Minus
      | Minus,Zero -> Bot,Bot
      | Minus,Plus -> Bot,Bot
      | Minus,Top -> Minus,Minus
      | Top,Zero -> Plus,Zero
      | Top,Plus -> Plus,Plus
      | _ -> s1,s2 end
    | AbstractSyntax.AST_GREATER_EQUAL ->
      begin match s1,s2 with
      | Bot,_ | _,Bot -> Bot,Bot
      | Zero,Plus -> Bot,Bot
      | Minus,Zero -> Bot,Bot
      | Minus,Plus -> Bot,Bot
      | Minus,Top -> Minus,Minus
      | Top,Plus -> Plus,Plus
      | _ -> s1,s2 end
    | AbstractSyntax.AST_LESS ->
      begin match s1,s2 with
      | Bot,_ | _,Bot -> Bot,Bot
      | Zero,Zero -> Bot,Bot
      | Zero,Minus -> Bot,Bot
      | Zero,Top -> Zero,Plus
      | Plus,Zero -> Bot,Bot
      | Plus,Plus -> Bot,Bot
      | Plus,Top -> Plus,Plus
      | Top,Zero -> Minus,Zero
      | Top,Minus -> Minus,Minus
      | _ -> s1,s2 end
    | AbstractSyntax.AST_LESS_EQUAL ->
      begin match s1,s2 with
      | Bot,_ | _,Bot -> Bot,Bot
      | Zero,Minus -> Bot,Bot
      | Plus,Zero -> Bot,Bot
      | Plus,Minus -> Bot,Bot
      | Plus,Top -> Plus,Plus
      | Top,Minus -> Minus,Minus
      | _ -> s1,s2 end

    let bwd_unary x op r =
      match op with
      | AbstractSyntax.AST_UNARY_PLUS -> meet x r
      | AbstractSyntax.AST_UNARY_MINUS -> meet x (unary r AbstractSyntax.AST_UNARY_MINUS)

    let bwd_binary x y op r =
      match op with
      | AST_PLUS -> meet (binary r y AST_MINUS) x, meet (binary r x AST_MINUS) y
      | AST_MINUS -> meet (binary r y AST_PLUS) x, meet (binary x r AST_MINUS) y
      | AST_MULTIPLY -> meet (binary r y AST_DIVIDE) x, meet (binary r x AST_DIVIDE) y
      | _ -> x,y
    
    let leq s1 s2 = match s1,s2 with
    | Bot,_ | _,Top -> true
    | _ -> s1 = s2

    let is_bottom = function
    | Bot -> false
    | _ -> false

    let pp fmt = function
      | Plus -> Format.fprintf fmt "Plus"
      | Minus -> Format.fprintf fmt "Minus"
      | Zero -> Format.fprintf fmt "0"
      | Top -> Format.fprintf fmt "Top"
      | Bot -> Format.fprintf fmt "Bottom"
  end: VALUE_DOMAIN)

module IntervalDomain =
  (struct
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


    let max_from_div b1 b2 = match b1,b2 with
      | PlusInf,PlusInf -> PlusInf
      | PlusInf,Value n -> 
          if Z.gt n Z.zero then PlusInf
          else MinusInf 
      | PlusInf,MinusInf -> MinusInf
      | MinusInf,PlusInf -> MinusInf
      | MinusInf,Value n ->
        if Z.lt n Z.zero then PlusInf
        else MinusInf
      | MinusInf,MinusInf -> PlusInf
      | Value n, _ when Z.equal n Z.zero -> Value Z.zero
      | Value n, PlusInf ->
        if Z.gt n Z.zero then PlusInf
        else MinusInf
      | Value n, MinusInf ->
        if Z.lt n Z.zero then PlusInf
        else MinusInf
      | Value n1, Value n2 ->
        Value (Z.div n1 n2)
    
    let min_from_div b1 b2 = match b1,b2 with
      | PlusInf,PlusInf -> PlusInf
      | PlusInf,Value n ->
        if Z.lt n Z.zero then MinusInf
        else PlusInf
      | PlusInf,MinusInf -> MinusInf
      | MinusInf,PlusInf -> MinusInf
      | MinusInf,MinusInf -> PlusInf
      | MinusInf,Value n -> 
        if Z.gt n Z.zero then MinusInf
        else PlusInf
      | Value n, _ when Z.equal n Z.zero -> Value Z.zero
      | Value n, PlusInf ->
        if Z.lt n Z.zero then MinusInf
        else PlusInf
      | Value n, MinusInf ->
        if Z.gt n Z.zero then MinusInf
        else PlusInf
      | Value n1, Value n2 ->
        Value (Z.div n1 n2)

    let interval_div int1 int2 = 
      match int1,int2 with
      | Empty,_ | _,Empty -> Empty
      | Interval (a,b), Interval (a',b') -> 
        if is_negative a' && is_positive b' then Interval (MinusInf,PlusInf)
        else
          Interval (
            border_min_list [min_from_div a a'; min_from_div a b'; min_from_div b a'; min_from_div b b'],
            border_max_list [max_from_div a a'; max_from_div a b'; max_from_div b a'; max_from_div b b']
          )
    
    type t = interval
    let top = Interval (MinusInf,PlusInf)
    let bottom = Empty
    let const n =
      Interval (Value n, Value n)
    let rand a b = 
      if Z.leq a b then Interval (Value a, Value b)
      else Empty
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
      | AbstractSyntax.AST_MULTIPLY -> 
        begin match y with
        | Empty -> Empty
        | Interval (a',b') -> if is_negative a' && is_positive b' then x
        else interval_intersect x (interval_div r y) end,
        begin match x with
        | Empty -> Empty
        | Interval (a',b') -> if is_negative a' && is_positive b' then y
        else interval_intersect y (interval_div r x) end
      | AbstractSyntax.AST_DIVIDE -> x,y
      | AbstractSyntax.AST_MODULO -> x,y
    let join = abstract_union
    let meet = interval_intersect
    let narrow = meet
    let widen int1 int2 =
      match int1,int2 with
      | Empty, i | i, Empty -> i
      | Interval (a1,b1), Interval (a2,b2) ->
        if border_ge a2 a1 && border_ge b1 b2 then int1
        else Interval ((if a1 <> a2 then MinusInf else a1), if b1 <> b2 then PlusInf else b1)
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
  end: VALUE_DOMAIN)

module CongruenceDomain = 
  (struct
    let rec pgcd a b =
      if Z.equal b Z.zero then a
      else pgcd b (Z.(mod) a b)

    let ppcm a b =
      if Z.equal a Z.zero || Z.equal b Z.zero then Z.zero
      else Z.div (pgcd a b) (Z.mul a b)

    let rec extended_pgcd a b =
      if Z.equal b Z.zero then (a,Z.one,Z.zero)
      else 
        let (p,u,v) = extended_pgcd b (Z.(mod) a b) in
        (p,v,Z.sub u (Z.mul (Z.div a b) v))

    type t =
    | Bottom
    | Congr of Z.t * Z.t (*Congr (a,b) represents aZ + b*)

    let top = Congr (Z.one,Z.zero)

    let bottom = Bottom

    let join c1 c2 = match c1,c2 with
    | Bottom,c | c,Bottom -> c
    | Congr (a1,b1), Congr (a2,b2) -> 
      Congr(pgcd (pgcd a1 a2) (Z.abs (Z.sub b1 b2)),b1)

    let meet c1 c2 = match c1,c2 with
    | Bottom,_ | _,Bottom -> bottom
    | Congr (a1,b1), Congr (a2,b2) ->
      if Z.equal a1 Z.zero && Z.equal a2 Z.zero then (
        if Z.equal b1 b2 then
          c1
        else bottom
      ) else
        let (p,u,v) = extended_pgcd a1 a2 in
        if Z.equal (Z.(mod) b1 p) (Z.(mod) b2 p) then
          Congr (ppcm a1 a2,Z.add b1 (Z.mul a1 (Z.mul u (Z.div (Z.sub b2 b1) p))))
        else top

    let widen = join

    let narrow c1 c2 = match c1,c2 with
    | Bottom,_ | _,Bottom -> bottom
    | Congr (a1,b1), _ -> 
      if Z.equal a1 Z.zero then c2
      else c1 

    let const n = Congr (Z.zero,n)

    let rand n1 n2 =
      if Z.equal n1 n2 then const n1 else top

    let unary c = function
      | AbstractSyntax.AST_UNARY_PLUS -> c
      | AbstractSyntax.AST_UNARY_MINUS ->
        begin match c with
        | Bottom -> Bottom
        | Congr (a,b) ->
          Congr (a,Z.sub a b)
        end

    let binary c1 c2 op =
      match (c1,c2) with
      | Bottom,_ | _,Bottom -> bottom
      | Congr (a1,b1), Congr(a2,b2) ->
        begin match op with
        | AbstractSyntax.AST_PLUS -> 
          Congr (pgcd a1 a2, Z.add b1 b2)
        | AbstractSyntax.AST_MINUS ->
          Congr (pgcd a1 a2, Z.add b1 (Z.sub a2 b2))
        | AbstractSyntax.AST_MULTIPLY ->
          Congr (pgcd (pgcd (Z.mul a1 a2) (Z.mul a1 b2)) (Z.mul b1 a2), Z.mul b1 b2)
        | AbstractSyntax.AST_DIVIDE ->
          if Z.equal a2 Z.zero && Z.equal b2 Z.zero then bottom
          else if Z.equal a2 Z.zero && Z.divisible a1 b2 && Z.divisible b1 b2 then Congr (Z.div a1 b2,Z.div b1 b2)
          else top
        | AbstractSyntax.AST_MODULO -> 
          if Z.equal a1 Z.zero && Z.equal a2 Z.zero then (
            if Z.equal Z.zero b2 then Bottom
            else Congr (Z.zero,Z.(mod) b1 b2)
          ) else
            top
        end

    let compare x y op = 
      match x,y with
      | Bottom,_ | _,Bottom -> bottom,bottom
      | Congr (a1,b1), Congr (a2,b2) ->
        begin match op with
        | AbstractSyntax.AST_EQUAL -> 
          let x' = meet x y in x',x'
        | AbstractSyntax.AST_NOT_EQUAL ->
          let x' =
            if Z.equal a2 Z.zero then
              if Z.equal a1 Z.zero then
                if not (Z.equal b1 b2) then
                  x
                else Bottom
              else x
            else x 
          in let y' =
            if Z.equal a1 Z.zero then
              if Z.equal a2 Z.zero then
                if not (Z.equal b1 b2) then
                  y
                else Bottom
              else y
            else y in
            x',y'
        | _ ->
          let (f1,f2) = 
            begin match op with
            | AbstractSyntax.AST_GREATER_EQUAL -> Z.geq, Z.leq
            | AbstractSyntax.AST_GREATER -> Z.gt, Z.lt
            | AbstractSyntax.AST_LESS_EQUAL -> Z.leq, Z.geq
            | AbstractSyntax.AST_LESS -> Z.lt, Z.gt
            | _ -> failwith "Cas impossible"
            end
          in
          let x' =
            if Z.equal a2 Z.zero then
              if Z.equal a1 Z.zero then
                if f1 b1 b2 then
                  x
                else Bottom
              else x
            else x 
          in let y' =
            if Z.equal a1 Z.zero then
              if Z.equal a2 Z.zero then
                if f2 b1 b2 then
                  y
                else Bottom
              else y
            else y in
            x',y'
        end

    let bwd_unary x op r =
      match op with
      | AbstractSyntax.AST_UNARY_PLUS -> meet x r
      | AbstractSyntax.AST_UNARY_MINUS -> meet x (unary r AbstractSyntax.AST_UNARY_MINUS)

    let bwd_binary x y op r =
      match op with
      | AST_PLUS -> meet (binary r y AST_MINUS) x, meet (binary r x AST_MINUS) y
      | AST_MINUS -> meet (binary r y AST_PLUS) x, meet (binary x r AST_MINUS) y
      | AST_MULTIPLY -> 
        begin match y with
        | Bottom -> Bottom
        | Congr (a,b) -> if Z.equal b Z.zero then x else meet (binary r y AST_DIVIDE) x end,
        begin match x with
        | Bottom -> Bottom
        | Congr (a,b) -> if Z.equal b Z.zero then y else meet (binary r x AST_DIVIDE) y end
      | _ -> x,y

    let leq c1 c2 = match c1,c2 with
    | Bottom,_ -> true
    | _,Bottom -> false
    | Congr (a1,b1), Congr (a2,b2) -> 
      if Z.equal a2 Z.zero then Z.equal a1 Z.zero && Z.equal b1 b2
      else Z.divisible a1 a2 && Z.equal (Z.(mod) (Z.sub b1 b2) a2) Z.zero

    let is_bottom = function
    | Bottom -> true
    | _ -> false

    let pp fmt = function
    | Bottom -> Format.fprintf fmt "Bottom"
    | Congr (a,b) ->
      Format.fprintf fmt "%sZ + %s" (Z.to_string a) (Z.to_string b)
  end: VALUE_DOMAIN)
