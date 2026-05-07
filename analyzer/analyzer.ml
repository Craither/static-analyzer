(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Simple driver: parses the file given as argument and prints it back.

  You should modify this file to call your functions instead!
*)

open Frontend

(* parse filename *)
let doit filename =
  let prog = FileParser.parse_file filename in
  let cfg = Tree_to_cfg.prog prog in
  if !Options.verbose then Format.printf "%a" ControlFlowGraphPrinter.print_cfg cfg ;
  ControlFlowGraphPrinter.output_dot !Options.cfg_out cfg ;
  Iterator.iterate cfg

(* parses arguments to get filename *)
let main () =
  let _ = Options.init () in
  doit !Options.file

let _ = main ()
