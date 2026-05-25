(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open ControlFlowGraph

module NSet = NodeSet
module NMap = NodeMap


let rec traverse n =
  match n.mark with
  | Visited -> ()
  | InProgress -> n.widen <- true
  | NotVisited -> (
    n.mark <- InProgress;
    List.iter (fun arc -> traverse arc.arc_dst) n.node_out;
    n.mark <- Visited
  )

let detect_cycles cfg =
  List.iter traverse cfg.cfg_nodes

let iterate cfg =
  detect_cycles cfg;
  let _ = Random.self_init () in
  let iter_arc arc : unit = match arc.arc_inst with _ -> failwith "TODO" in
  let iter_node node : unit = Format.printf "<%i>: ⊤@ " node.node_id in
  List.iter iter_arc cfg.cfg_arcs ;
  Format.printf "Node Values:@   @[<v 0>" ;
  List.iter iter_node cfg.cfg_nodes ;
  Format.printf "@]"

