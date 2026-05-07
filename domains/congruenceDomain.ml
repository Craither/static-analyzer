open Frontend

type congruence =
    Bottom
  | Congr of Z.t * Z.t

module CongruenceDomain =
  struct
    type t = congruence

    let top  = Congr (Z.one,Z.zero)

    let bottom = Bottom

    let const = failwith "TODO"

    let rand = failwith "TODO"

    let unary = failwith "TODO"

    let binary = failwith "TODO"

    let compare = failwith "TODO"

    let bwd_unary = failwith "TODO"

    let bwd_binary = failwith "TODO"

    let join = failwith "TODO"

    let meet = failwith "TODO"

    (* widening *)
    let widen = failwith "TODO"

    (* narrowing *)
    let narrow = failwith "TODO"

    let leq = failwith "TODO"

    let is_bottom = failwith "TODO"

    let pp = failwith "TODO"
  end