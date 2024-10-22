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

type sentence_kind = Proof | Qed | Other

let get_sentence_kind = function
  | Ser.[ ObjList [ CoqAst vernac ]; Completed ] -> (
      match vernac.v.expr with
      | Vernacexpr.VernacProof _ -> Proof
      | Vernacexpr.(VernacEndProof (Proved _)) -> Qed
      | _ -> Other)
  | _ -> Other

(* sentences between `Proof.` and `Qed.`, include `Proof.` *)
let filter_proofs sentence_kinds =
  let rec aux proofs cur_proof = function
    | (s, Proof) :: rest -> aux proofs [ s ] rest
    | (s, Other) :: rest -> aux proofs (s :: cur_proof) rest
    | (_, Qed) :: rest -> aux (List.rev cur_proof :: proofs) [] rest
    | [] -> List.rev proofs
  in
  aux [] [] sentence_kinds

let get_goal_tactic_pairs proof =
  let open SerST in
  let rec aux result = function
    | s1 :: s2 :: rest -> (
        let* goals = ser_exec (query_goals_str s1.id) in
        match goals with
        | Ser.[ ObjList [ CoqString goal ]; Completed ] ->
            aux ((goal, s2.text) :: result) (s2 :: rest)
        | _ -> aux result (s2 :: rest))
    | _ -> return (List.rev result)
  in
  aux [] proof

let main input_file ml_path vo_path1 vo_path2 =
  let sentences, init_state = ser_init input_file ml_path vo_path1 vo_path2 in
  let test =
    let open SerST in
    let* _ = mapM (fun s -> ser_exec (Ser.Exec s.id)) sentences in
    let* sentence_kinds =
      mapM
        (fun s ->
          let* ans = ser_exec (query_sentence_ast s.id) in
          return (s, get_sentence_kind ans))
        sentences
    in
    let proofs = filter_proofs sentence_kinds in
    let* goal_tactic_pairs = List.flatten $ mapM get_goal_tactic_pairs proofs in
    let _ =
      List.iter
        (fun (goal, tac) ->
          print_endline "######## GOAL ########";
          print_endline goal;
          print_endline "####### TACTIC #######";
          print_endline tac;
          print_endline "")
        goal_tactic_pairs
    in
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
