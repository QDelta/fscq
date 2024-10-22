open Serapi
open Sertop
open Serapitest
module Ser = Serapi_protocol

type sentence = {id: Stateid.t; text: string}

let get_sentences file_content add_answers =
  add_answers
  |> List.filter_map (function
       | Ser.Added (sid, loc, _) ->
           Some {id= sid; text= String.sub file_content loc.bp (loc.ep - loc.bp)}
       | _ ->
           None )

let ser_init input_file ml_path vo_path =
  (* make sexp print less verbose *)
  Serlib.Serlib_init.(
    init
      ~options:
        {omit_loc= true; omit_att= true; omit_env= true; exn_on_opaque= false} ) ;
  let default_ml_path, default_vo_path =
    Serapi_paths.coq_loadpath_default ~implicit:true
      ~coq_path:
        ( match Sys.getenv_opt "COQLIB" with
        | Some coqlib ->
            coqlib
        | None ->
            Coq_config.coqlib )
  in
  Sertop_init.(
    coq_init
      { fb_handler= (fun _ _ -> ())
      ; plugin_load= None
      ; debug= false
      ; set_impredicative_set= false
      ; allow_sprop= false
      ; indices_matter= false
      ; ml_path= default_ml_path @ ml_path
      ; vo_path= default_vo_path @ vo_path }
      Format.std_formatter ) ;
  let injections =
    [Coqargs.RequireInjection ("Coq.Init.Prelude", None, Some Lib.Import)]
  in
  let stm_options = Stm.AsyncOpts.default_opts in
  let doc_type =
    Stm.Interactive (Coqargs.TopPhysical input_file)
    (* Stm.Interactive (TopLogical Names.(DirPath.make [ Id.of_string "SerApiTest" ])) *)
  in
  Stm.(new_doc {doc_type; injections; stm_options}) |> ignore ;
  let empty_state =
    Ser.State.make ~in_file:input_file
      ~ldir:(Serapi_paths.dirpath_of_file input_file)
      ()
  in
  let file_content =
    let in_chan = open_in input_file in
    let content = In_channel.input_all in_chan in
    close_in in_chan ; content
  in
  let add_opts = Ser.{lim= None; ontop= None; newtip= None; verb= false} in
  let answers, init_state =
    Ser.exec_cmd empty_state (Ser.Add (add_opts, file_content))
  in
  (get_sentences file_content answers, init_state)

module SerST = Statem.Make (struct
  type st = Ser.State.t
end)

let ser_exec cmd : Ser.answer_kind list SerST.t = fun st -> Ser.exec_cmd st cmd

let get_ctx sid =
  sid |> Stm.state_of_id ~doc:(Stm.get_doc 0) |> Extcoq.context_of_st

let format_ser =
  Ser.{pp_format= PpSer; pp_depth= 0; pp_elide= "..."; pp_margin= 0}

type proof_ctx = {hyps: string; goal: string} [@@deriving yojson]

type tactic_record = {ctx: proof_ctx list; tactic: string} [@@deriving yojson]

let query_proof_ctx sid =
  let open SerST in
  let query =
    Ser.(Query ({preds= []; limit= None; sid; pp= format_ser; route= 0}, Goals))
  in
  let* ans = ser_exec query in
  let sigma, env = get_ctx sid in
  match ans with
  | Ser.[ObjList [CoqGoal g]; Completed] ->
      return
        (Some
           (List.map
              (fun g ->
                let hyps, goal = Serpp.pp_coq_goal_str env sigma format_ser g in
                {hyps; goal} )
              g.Serapi_goals.goals ) )
  | _ ->
      return None

let query_sentence_ast sid =
  let query =
    Ser.(Query ({preds= []; limit= None; sid; pp= format_ser; route= 0}, Ast))
  in
  ser_exec query

type sentence_kind = Proof | Qed | Other

let get_sentence_kind = function
  | Ser.[ObjList [CoqAst vernac]; Completed] -> (
    match vernac.v.expr with
    | Vernacexpr.VernacProof _ ->
        Proof
    | Vernacexpr.(VernacEndProof (Proved _)) ->
        Qed
    | _ ->
        Other )
  | _ ->
      Other

(* sentences between `Proof.` and `Qed.`, include `Proof.` *)
let filter_proofs sentence_kinds =
  let rec aux proofs cur_proof = function
    | (s, Proof) :: rest ->
        aux proofs [s] rest
    | (s, Other) :: rest ->
        aux proofs (s :: cur_proof) rest
    | (_, Qed) :: rest ->
        aux (List.rev cur_proof :: proofs) [] rest
    | [] ->
        List.rev proofs
  in
  aux [] [] sentence_kinds

let get_tactic_record proof =
  let open SerST in
  let rec aux result = function
    | s1 :: s2 :: rest -> (
        let* ctx = query_proof_ctx s1.id in
        match ctx with
        | Some ctx ->
            aux ({ctx; tactic= s2.text} :: result) (s2 :: rest)
        | None ->
            aux result (s2 :: rest) )
    | _ ->
        return (List.rev result)
  in
  aux [] proof

let print_exn i = function
  | Ser.CoqExn info ->
      ( match info.loc with
      | Some loc ->
          Format.printf "line %i " loc.line_nb
      | None ->
          () ) ;
      Format.printf "(sentence %i) " i ;
      Format.print_flush () ;
      print_endline info.str
  | _ ->
      ()

let main input_file output_file ml_path vo_path1 vo_path2 =
  let sentences, init_state =
    ser_init input_file ml_path (vo_path1 @ vo_path2)
  in
  let test =
    let open SerST in
    let* exec_answers = mapM (fun s -> ser_exec (Ser.Exec s.id)) sentences in
    List.iteri (fun i ans -> List.iter (print_exn i) ans) exec_answers ;
    let* sentence_kinds =
      mapM
        (fun s ->
          let* ans = query_sentence_ast s.id in
          return (s, get_sentence_kind ans) )
        sentences
    in
    let proofs = filter_proofs sentence_kinds in
    let* tactic_records = List.flatten $ mapM get_tactic_record proofs in
    let output_chan = open_out output_file in
    List.iter
      (fun tr ->
        Yojson.Safe.to_channel ~suf:"\n" output_chan
          (tactic_record_to_yojson tr) )
      tactic_records ;
    close_out output_chan ;
    return ()
  in
  SerST.run test init_state

let main_cmd =
  let open Sertop_arg in
  let open Cmdliner in
  let input_file =
    let doc = "Input file" in
    Arg.(required & pos 0 (some string) None & info [] ~docv:"INPUT_FILE" ~doc)
  in
  let output_file =
    let doc = "Output file" in
    Arg.(required & pos 1 (some string) None & info [] ~docv:"OUTPUT_FILE" ~doc)
  in
  let term =
    Term.(
      const main $ input_file $ output_file $ ml_include_path $ load_path
      $ rload_path )
  in
  let info = Cmd.info "serapitest" in
  Cmd.v info term

let _ = exit (Cmdliner.Cmd.eval main_cmd)
