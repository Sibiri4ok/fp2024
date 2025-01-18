(** Copyright 2024-2025, Danil Usoltsev *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open EUsoltsev_lib
open Inferencer
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
           not (List.mem key [ "print_int"; "print_endline"; "print_bool" ]))
       in
       Base.Map.iteri filtered_env ~f:(fun ~key:_ ~data:(S (_, ty)) ->
         Format.printf "%a\n" pp_ty ty)
     | Error e -> Format.printf "Infer error. %a\n" pp_error e)
  | Error e -> Format.printf "Parsing error. %s\n" e
;;

let%expect_test "test_1" =
  pretty_printer_parse_and_infer
    "let fac n = if n<=1 then 1 else n * fac (n-1)";
  [%expect {|intе|}]
;;

let%expect_test "test_2" =
  pretty_printer_parse_and_infer
    "let rec fac_cps n k =\n\
    \  if n=1 then k 1 else\n\
    \  fac_cps (n-1) (fun p -> k (p*n))\n\
    \  \n\
    \  let main =\n\
    \  let () = print_int (fac_cps 4 (fun print_int -> print_int)) in\n\
    \  0";
  [%expect {|int|}]
;;

let%expect_test "test_3" =
  pretty_printer_parse_and_infer
    "let rec fib_acc a b n =\n\
    \  if n=1 then b\n\
    \  else\n\
    \    let n1 = n-1 in\n\
    \    let ab = a+b in\n\
    \    fib_acc b ab n1\n\n\
     let rec fib n =\n\
    \  if n<2\n\
    \  then n\n\
    \  else fib (n - 1) + fib (n - 2) \n\n\
     let main =\n\
    \  let () = print_int (fib_acc 0 1 4) in\n\
    \  let () = print_int (fib 4) in\n\
    \  0";
  [%expect {|int|}]
;;

let%expect_test "test_4" =
  pretty_printer_parse_and_infer
    "let wrap f = if 1 = 1 then f else f\n\n\
     let test3 a b c =\n\
    \  let a = print_int a in\n\
    \  let b = print_int b in\n\
    \  let c = print_int c in\n\
    \  0\n\n\
     let test10 a b c d e f g h i j = a + b + c + d + e + f + g + h + i + j\n\n\
     let main =\n\
    \  let rez =\n\
    \      (wrap test10 1 10 100 1000 10000 100000 1000000 10000000 100000000\n\
    \         1000000000)\n\
    \  in\n\
    \  let () = print_int rez in\n\
    \  let temp2 = wrap test3 1 10 100 in\n\
    \  0";
  [%expect {|intt|}]
;;

let%expect_test "test_5" =
  pretty_printer_parse_and_infer
    "let rec fix f x = f (fix f) x\n\n\
     let fac self n = if n<=1 then 1 else n * self (n-1)\n\n\
     let main =\n\
    \  let () = print_int (fix fac 6) in\n\
    \  0";
  [%expect {|intt|}]
;;

let%expect_test "test_6" =
  pretty_printer_parse_and_infer
    "let foo b = if b then (fun foo -> foo+2) else (fun foo -> foo*10)\n\n\
     let foo x = foo true (foo false (foo true (foo false x)))\n\
     let main =\n\
    \  let () = print_int (foo 11) in\n\
    \  0";
  [%expect {|intt|}]
;;

let%expect_test "test_7" =
  pretty_printer_parse_and_infer
    "let foo a b c =\n\
    \  let () = print_int a in\n\
    \  let () = print_int b in\n\
    \  let () = print_int c in\n\
    \  a + b * c\n\n\
     let main =\n\
    \  let foo = foo 1 in\n\
    \  let foo = foo 2 in\n\
    \  let foo = foo 3 in\n\
    \  let () = print_int foo in\n\
    \  0";
  [%expect {|intt|}]
;;

let%expect_test "test_8" =
  pretty_printer_parse_and_infer
    "let foo a =\n\
    \  let () = print_int a in fun b ->\n\
    \  let () = print_int b in fun c ->\n\
    \  print_int c\n\n\
     let main =\n\
    \  let () = foo 4 8 9 in\n\
    \  0";
  [%expect {|intt|}]
;;

let%expect_test "test_9" =
  pretty_printer_parse_and_infer
    "let _start () () a () b _c () d __ =\n\
    \  let () = print_int (a+b) in\n\
    \  let () = print_int __ in\n\
    \  a*b / _c + d\n\n\n\
     let main =\n\
    \  print_int (_start (print_int 1) (print_int 2) 3 (print_int 4) 100 1000 (print_int \
     (-1)) 10000 (-555555))";
  [%expect {|intt|}]
;;

let%expect_test "test_8ascription" =
  pretty_printer_parse_and_infer
    "let addi = fun f g x -> (f x (g x: bool) : int)\n\n\
     let main =\n\
    \  let () = print_int (addi (fun x b -> if b then x+1 else x*2) (fun _start -> \
     _start/2 = 0) 4) in\n\
    \  0";
  [%expect {|intt|}]
;;

let%expect_test "test_15tuples" =
  pretty_printer_parse_and_infer "let () = (fun x -> x)";
  [%expect
    {|
    (\140 -> \141 -> int * \142 -> \143 -> int)
    ~ -> \127 -> int
    ((c -> d) -> c -> d) -> c -> d
    m -> (x * x)
    \132 -> \133 -> int
    g -> h -> (k * k)
    \138 -> (\139 * \139)|}]
;;

let%expect_test "test_binary_oper" =
  pretty_printer_parse_and_infer "10/2 + 56*2 - 10 / 10 / 20 + 666 - 777 + 1";
  [%expect {|int|}]
;;

let%expect_test "test_bool" =
  pretty_printer_parse_and_infer "false";
  [%expect {|bool|}]
;;

let%expect_test "test_string" =
  pretty_printer_parse_and_infer "\"I like OCaml\" ";
  [%expect {|string|}]
;;

let%expect_test "test_option" =
  pretty_printer_parse_and_infer "Some 10";
  [%expect {|int option|}]
;;

let%expect_test "test_binary_oper_and_arg" =
  pretty_printer_parse_and_infer "fun x -> x * 69 + 100 - 201 / 777";
  [%expect {|a -> int|}]
;;

let%expect_test "test_binary_oper_and_arg" =
  pretty_printer_parse_and_infer "fun x -> x * 69 + 100 - 201 / 777";
  [%expect {|a -> int|}]
;;

let%expect_test "test_rec" =
  pretty_printer_parse_and_infer "let rec func arg = func arg";
  [%expect {|b -> c|}]
;;

let%expect_test "test_func_apply_some_args" =
  pretty_printer_parse_and_infer "let func a1 a2 a3 = a1 a2 a3";
  [%expect {|a -> b -> c -> d|}]
;;

let%expect_test "test_tuple" =
  pretty_printer_parse_and_infer "fun x y z -> (x + 10, y / 2 , z)";
  [%expect {|a -> b -> c -> (int * int * c)|}]
;;

let%expect_test "test_list" =
  pretty_printer_parse_and_infer "let arr = [1;2;3]";
  [%expect {|int list|}]
;;

let%expect_test "test_binary_oper" =
  pretty_printer_parse_and_infer "let is_above_10 x = if x > 10 then true else false ";
  [%expect {|a -> bool|}]
;;

let%expect_test "test_binary_oper" =
  pretty_printer_parse_and_infer "let is_above_10 x = x > 10";
  [%expect {|a -> bool|}]
;;

let%expect_test "test_factorial" =
  pretty_printer_parse_and_infer "let rec fac n = if n < 2 then 1 else n * fac (n - 1)";
  [%expect {|int -> int|}]
;;

let%expect_test "test_fibonacci" =
  pretty_printer_parse_and_infer
    "let rec fibo n = if n < 2 then 1 else fibo(n - 1) + fibo(n - 2)";
  [%expect {|int -> int|}]
;;

let%expect_test "test_unbound_var" =
  pretty_printer_parse_and_infer "let f = x";
  [%expect {|Infer error. Unbound variable 'x'.|}]
;;

let%expect_test "test_annotate" =
  pretty_printer_parse_and_infer "let sum (x : int) (y : int) = x + y";
  [%expect {|int -> int -> int|}]
;;

let%expect_test "test_annotate_fac" =
  pretty_printer_parse_and_infer
    "let rec fac (n : int) (acc : int) = if n < 2 then acc else fac (n-1) (acc * n);;";
  [%expect {|int -> int -> int|}]
;;

let%expect_test "test_program_1" =
  pretty_printer_parse_and_infer
    "let div = fun x y -> x / y;; let sum = fun x y -> x + y;; let res = fun x y z ->  \
     div x (sum y z)";
  [%expect {|
    a -> b -> int
    e -> f -> g -> int
    c -> d -> int|}]
;;

let%expect_test "test_program_2" =
  pretty_printer_parse_and_infer "let square = fun x -> x * x ;; let result = square 10";
  [%expect {|
    int
    a -> int|}]
;;

let%expect_test "test_annotate_error" =
  pretty_printer_parse_and_infer "let sum (x : int) (y : string) = x + y";
  [%expect {|Infer error. Failed to unify types: string and int.|}]
;;

let%expect_test "test_unification_types" =
  pretty_printer_parse_and_infer "fun x -> x + true";
  [%expect {|Infer error. Failed to unify types: bool and int.|}]
;;

(*  PASSED let%expect_test "test_unification_types" =
    pretty_printer_parse_and_infer "let temp =
    let f = fun x -> x in
    (f 1, f true)";
    [%expect {|Infer error. Failed to unify types: bool and int.|}]
    ;; *)
