(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open ControlFlowGraph
open Domains

module MyVars : Domain.VARS = struct
  let support = []
end

module Domain = Domain.Value_to_Domain(ValueDomain.CongruenceDomain)(MyVars)

(*module Domain = Domain.PolyhedraDomain(MyVars)*)

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
            Printf.printf "File \"%s\", line %d: Assertion failure" pos.pos_fname pos.pos_lnum;
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
        let new_env_dst = 
          if node.widen then 
           Domain.widen env_dst new_env_dst
          else
           Domain.join env_dst new_env_dst
        in
        (NMap.add arc.arc_dst new_env_dst program_env, (changed || not (Domain.leq env_dst new_env_dst)))
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
  let default_state = start_exec cfg.cfg_init_entry Domain.bottom NMap.empty in (*we initialize all the variables*)
  let default_value = NMap.find cfg.cfg_init_exit default_state in
  List.fold_left ( (*we test each function*)
  fun program_env f -> 
    start_exec f.func_entry default_value program_env) 
  initial_state cfg.cfg_funcs;
  (*
  let iter_node node : unit = Format.printf "<%i>: ⊤@ " node.node_id in List.iter iter_node cfg.cfg_nodes*)

