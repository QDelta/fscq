open Serapi
open Sertop
module Ser = Serapi_protocol

type sentence = { id : Stateid.t; text : string }

let get_sentences file_content add_answers =
  add_answers
  |> List.filter_map (function
       | Ser.Added (sid, loc, _) ->
           Some
             {
               id = sid;
               text = String.sub file_content loc.bp (loc.ep - loc.bp);
             }
       | _ -> None)
  |> Array.of_list

let ser_init input_file ml_path vo_path1 vo_path2 =
  let _ =
    (* make sexp print less verbose *)
    Serlib.Serlib_init.(
      init
        ~options:
          {
            omit_loc = true;
            omit_att = true;
            omit_env = true;
            exn_on_opaque = false;
          })
  in
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
    Stm.Interactive (Coqargs.TopPhysical input_file)
    (* Stm.Interactive (TopLogical Names.(DirPath.make [ Id.of_string "SerApiTest" ])) *)
  in
  let _ = Stm.(new_doc { doc_type; injections; stm_options }) in
  let empty_state =
    Ser.State.make ~in_file:input_file
      ~ldir:(Serapi_paths.dirpath_of_file input_file)
      ()
  in
  let file_content =
    let in_chan = open_in input_file in
    let content = In_channel.input_all in_chan in
    close_in in_chan;
    content
  in
  let add_opts =
    Ser.{ lim = None; ontop = None; newtip = None; verb = false }
  in
  let answers, init_state =
    Ser.exec_cmd empty_state (Ser.Add (add_opts, file_content))
  in
  (get_sentences file_content answers, init_state)

module SerST = Statem.Make (struct
  type st = Ser.State.t
end)

let ser_exec cmd : Ser.answer_kind list SerST.t = fun st -> Ser.exec_cmd st cmd

let ser_exec_print cmd : unit SerST.t =
  let open SerST in
  let* answers = ser_exec cmd in
  List.iter
    (fun ans ->
      let sexp = Sertop_ser.sexp_of_answer_kind ans in
      print_endline (Sexplib0.Sexp.to_string_hum sexp))
    answers;
  return ()

let format_str =
  Ser.{ pp_format = PpStr; pp_depth = 0; pp_elide = "..."; pp_margin = 72 }

let format_ast =
  Ser.{ pp_format = PpSer; pp_depth = 0; pp_elide = "..."; pp_margin = 72 }

let query_goals_str sid =
  Ser.(
    Query ({ preds = []; limit = None; sid; pp = format_str; route = 0 }, Goals))

let query_sentence_ast sid =
  Ser.(
    Query ({ preds = []; limit = None; sid; pp = format_ast; route = 0 }, Ast))

let is_proof_start = function
  | Ser.ObjList [ Ser.CoqAst vernac ] -> (
      match vernac.v.expr with Vernacexpr.VernacProof _ -> true | _ -> false)
  | _ -> false

let is_qed = function
  | Ser.ObjList [ Ser.CoqAst vernac ] -> (
      match vernac.v.expr with
      | Vernacexpr.(VernacEndProof (Proved _)) -> true
      | _ -> false)
  | _ -> false

let main input_file ml_path vo_path1 vo_path2 =
  let sentences, init_state = ser_init input_file ml_path vo_path1 vo_path2 in
  let test =
    let open SerST in
    let _ = Array.iter (fun s -> print_endline s.text) sentences in
    let* _ = ser_exec_print (query_goals_str sentences.(1).id) in
    let* _ = ser_exec_print (query_sentence_ast sentences.(2).id) in
    return ()
  in
  SerST.run test init_state

let main_cmd =
  let open Sertop_arg in
  let open Cmdliner in
  let input_file =
    let doc = "Input file" in
    Arg.(required & pos 0 (some string) None & info [] ~docv:"FILE" ~doc)
  in
  let term =
    Term.(const main $ input_file $ ml_include_path $ load_path $ rload_path)
  in
  let info = Cmd.info "serapitest" in
  Cmd.v info term

let _ = exit (Cmdliner.Cmd.eval main_cmd)
