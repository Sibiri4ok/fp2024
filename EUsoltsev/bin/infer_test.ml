open EUsoltsev_lib
open Inferencer
open Typing
open Parser
open Printf
open Ast

let parse_test input =
  match parse input with
  | Ok ast -> printf "%s\n" (show_program ast)
  | Error fail -> printf "%s\n" fail
;;

let pretty_printer_parse_and_infer s =
  match Parser.parse s with
  | Ok parsed ->
    (match run_infer parsed with
     | Ok env ->
       let filtered_env =
         Base.Map.filter_keys env ~f:(fun key ->
           not (List.mem key ["print_int"; "print_endline"; "print_bool"]))
       in
       Base.Map.iteri filtered_env ~f:(fun ~key:_ ~data:(S (_, ty)) ->
         Format.printf "%a\n" pp_ty ty)
     | Error e -> Format.printf "Infer error. %a\n" pp_error e)
  | Error e -> Format.printf "Parsing error. %s\n" e
;;

let () = pretty_printer_parse_and_infer 