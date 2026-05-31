(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open ControlFlowGraph
open Domains
open Lexing

module MyVars : Domain.VARS = struct
  let support = []
end

module NSet = NodeSet
module NMap = NodeMap

let domains : (module Domain.DOMAIN) list =
  [
    (module Domain.Value_to_Domain(ValueDomain.IntervalDomain)(MyVars) : Domain.DOMAIN);
    (module Domain.Value_to_Domain(ValueDomain.CongruenceDomain)(MyVars) : Domain.DOMAIN);
    (module Domain.Value_to_Domain(ValueDomain.SignDomain)(MyVars) : Domain.DOMAIN)
  ]

module PosSet = struct
  type t = (Lexing.position, unit) Hashtbl.t
  let create n = Hashtbl.create n
  let add s x = Hashtbl.replace s x ()
  let remove s x = Hashtbl.remove s x
  let iter f s =  Hashtbl.iter (fun pos () -> f pos) s
  let mem s x = Hashtbl.mem s x
  let inter a b =
    let r = Hashtbl.create (min (Hashtbl.length a) (Hashtbl.length b)) in
    Hashtbl.iter
      (fun k v ->
         if Hashtbl.mem b k then
           Hashtbl.add r k v)
      a;
    r
end

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

let error_domain cfg (module Domain : Domain.DOMAIN) =
  detect_cycles cfg;
  let failed_assert = PosSet.create 64 in
  let rec update to_update program_env = 
    match NSet.min_elt_opt to_update with
    | None -> program_env (*we've found a fix point*)
    | Some node -> 
      let to_update = NSet.remove node to_update in 
      let update_env env inst =
        match inst with 
        | CFG_skip _ -> 
          env
        
        | CFG_assign(v, int_expr) ->
          Domain.assign env v int_expr
           
        | CFG_guard bool_expr ->
          Domain.guard env bool_expr
          
        | CFG_assert(bool_expr, (pos, _)) ->
          let not_bool_expr = CFG_bool_unary(AST_NOT, bool_expr) in 
          begin
          if not (Domain.is_bottom (Domain.guard env not_bool_expr)) then
            PosSet.add failed_assert pos;
          end;
          Domain.guard env bool_expr
	      
        | CFG_call _ -> failwith "TODO"
        
      in
      let new_env, changed = List.fold_left 
      (fun (program_env, changed) arc -> 
        let env_src = match NMap.find_opt arc.arc_src program_env with
          | None -> Domain.bottom
          | Some env_src -> env_src
        in
        let env_dst = match NMap.find_opt arc.arc_dst program_env with
          | None -> Domain.bottom
          | Some env_dst -> env_dst
        in
        let new_env_dst = update_env env_src arc.arc_inst in
        let new_env_dst = Domain.join env_dst new_env_dst in
        let new_env_dst = 
          if node.widen then 
           Domain.widen env_dst new_env_dst
          else
           new_env_dst
        in

        (NMap.add arc.arc_dst new_env_dst program_env, (changed || not (Domain.leq new_env_dst env_dst)))
      )
      program_env node.node_in
      in
      Printf.printf "%d\n" node.node_id;
      let env = match NMap.find_opt node (fst program_env) with
        | None -> Domain.bottom
        | Some env_src -> env_src
      in
      Domain.pp (Format.std_formatter) env;
      Format.fprintf (Format.std_formatter) "\n";
      Format.pp_print_flush (Format.std_formatter) ();
      let env = match NMap.find_opt node new_env with
        | None -> Domain.bottom
        | Some env_src -> env_src
      in
      Domain.pp (Format.std_formatter) env;
      Format.fprintf (Format.std_formatter) "\n";
      Format.pp_print_flush (Format.std_formatter) ();
      
      Printf.printf "%b\n" changed;
      let to_update =
        if changed || not (NMap.mem node (fst program_env)) then 
          List.fold_left (
          fun to_update arc -> 
            NSet.add arc.arc_dst to_update
          ) 
          to_update node.node_out
        else
          to_update
      in
      update to_update (new_env, false)
  in
  let start_exec node _ program_env = 
    let to_update = NSet.of_list [node] in
    (*let program_env = NMap.add node default_value program_env in*)
    fst (update to_update (program_env, false))
  in
  let initial_state = start_exec cfg.cfg_init_entry Domain.init NMap.empty in (*we initialize all the variables*)
  let default_value = NMap.find cfg.cfg_init_exit initial_state in
  let _ = List.fold_left ( (*we test each function*)
  fun program_env f -> 
    start_exec f.func_entry default_value program_env) 
  initial_state cfg.cfg_funcs
  in
  failed_assert
  

let iterate cfg = 
  let all_asserts = PosSet.create 64 in
  List.iter (
  fun arc -> 
    match arc.arc_inst with 
    | CFG_assert(_, (pos, _)) -> PosSet.add all_asserts pos
    | _ -> ()
  ) cfg.cfg_arcs;
  let failed_assert = List.fold_left (
  fun assert_list domain -> 
    PosSet.inter (error_domain cfg domain) assert_list
  ) all_asserts domains in
  
  PosSet.iter (fun pos -> Printf.printf "File \"%s\", line %d: Assertion failure" pos.pos_fname pos.pos_lnum) failed_assert;

