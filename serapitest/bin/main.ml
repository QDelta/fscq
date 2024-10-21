open Serapi
open Sertop
module Ser = Serapi_protocol

let ser_init ml_path vo_path1 vo_path2 =
  let default_ml_path, default_vo_path =
    Serapi_paths.coq_loadpath_default ~implicit:true
      ~coq_path:
        (match Sys.getenv_opt "COQLIB" with
        | Some coqlib -> coqlib
        | None -> Coq_config.coqlib)
  in
  let _ =
    Sertop_init.(
      coq_init
        {
          fb_handler = (fun _ _ -> ());
          plugin_load = None;
          debug = false;
          set_impredicative_set = false;
          allow_sprop = false;
          indices_matter = false;
          ml_path = default_ml_path @ ml_path;
          vo_path = default_vo_path @ vo_path1 @ vo_path2;
        }
        Format.std_formatter)
  in
  let injections =
    [ Coqargs.RequireInjection ("Coq.Init.Prelude", None, Some Lib.Import) ]
  in
  let stm_options = Stm.AsyncOpts.default_opts in
  let doc_type =
    Stm.Interactive
      (TopLogical Names.(DirPath.make [ Id.of_string "SerApiTest" ]))
  in
  let _ = Stm.(new_doc { doc_type; injections; stm_options }) in
  Ser.State.make ()

let string_of_answer_kind k =
  let sexp = Sertop_ser.sexp_of_answer_kind k in
  Sexplib0.Sexp.to_string_hum sexp

let exec_and_print state cmd =
  let answers, state = Ser.exec_cmd state cmd in
  List.iter (fun k -> print_endline (string_of_answer_kind k)) answers;
  state

let format_str =
  Ser.{ pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 }

let format_ast =
  Ser.{ pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 }

let main ml_path vo_path1 vo_path2 =
  let state0 = ser_init ml_path vo_path1 vo_path2 in
  let add_opts =
    Ser.{ lim = None; ontop = None; newtip = None; verb = false }
  in
  let state1 =
    exec_and_print state0
      (Ser.Add (add_opts, "Goal True. Proof. apply I. Qed."))
  in
  let state2 = exec_and_print state1 (Ser.Exec (Stateid.of_int 5)) in
  let state3 =
    exec_and_print state2
      Ser.(
        Query
          ( {
              preds = [];
              limit = None;
              sid = Stateid.of_int 3;
              pp = format_ast;
              route = 0;
            },
            Ast ))
  in
  ignore state3

let main_cmd =
  let open Sertop_arg in
  let term =
    Cmdliner.Term.(const main $ ml_include_path $ load_path $ rload_path)
  in
  let info = Cmdliner.Cmd.info "serapitest" in
  Cmdliner.Cmd.v info term

let _ = exit (Cmdliner.Cmd.eval main_cmd)
