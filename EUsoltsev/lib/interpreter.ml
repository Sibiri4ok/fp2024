(** Copyright 2024-2025, Danil Usoltsev *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast
open Base
open Format
open Pprinter

type env = (ident, value, String.comparator_witness) Map.t

and value =
  | ValueInt of int
  | ValueBool of bool
  | ValueString of string
  | ValueUnit
  | ValueClosure of pattern * is_rec * expr * env
  | ValueTuple of value * value * value list
  | ValueList of value list
  | ValueBuiltin of (value -> (value, value_error) Result.t)

and value_error =
  | UnboundVariable of ident
  | TypeError of value
  | DivisionByZeroError
  | PatternMatchingError
  | NotImplemented

let rec pp_value ppf = function
  | ValueInt x -> fprintf ppf "%d" x
  | ValueBool b -> fprintf ppf "%b" b
  | ValueString s -> fprintf ppf "\"%s\"" s
  | ValueUnit -> fprintf ppf "()"
  | ValueTuple (v1, v2, vl) ->
    fprintf
      ppf
      "(%a, %a%a)"
      pp_value
      v1
      pp_value
      v2
      (fun ppf -> function
        | [] -> ()
        | l ->
          fprintf
            ppf
            ", %a"
            (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_value)
            l)
      vl
  | ValueList vl ->
    fprintf
      ppf
      "[%a]"
      (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ") pp_value)
      vl
  | ValueClosure _ -> fprintf ppf "<fun>"
  | ValueBuiltin _ -> fprintf ppf "<builtin>"
;;

let pp_value_error fmt = function
  | UnboundVariable ident -> fprintf fmt "UnboundVariable: %S" ident
  | TypeError err_val -> fprintf fmt "TypeError: %a" pp_value err_val
  | DivisionByZeroError -> fprintf fmt "DivisionByZeroError"
  | PatternMatchingError -> fprintf fmt "PatternMatchingError"
  | NotImplemented -> fprintf fmt "NotImplemented"
;;

module type Monad = sig
  type ('a, 'e) t

  val return : 'a -> ('a, 'e) t
  val fail : 'e -> ('a, 'e) t
  val ( let* ) : ('a, 'e) t -> ('a -> ('b, 'e) t) -> ('b, 'e) t
end

module Env (M : Monad) = struct
  open M

  let empty = Base.Map.empty (module Base.String)
  let extend env key value = Base.Map.update env key ~f:(fun _ -> value)

  let find map key =
    match Base.Map.find map key with
    | Some value -> return value
    | None -> fail (UnboundVariable key)
  ;;
end

module Eval (M : Monad) : sig
  val eval_structure : program -> (env, value_error) M.t
end = struct
  open M
  open Env (M)

  let initial_env =
    let open Base.Map in
    empty (module String)
    |> set
         ~key:"print_int"
         ~data:
           (ValueBuiltin
              (function
                | ValueInt i ->
                  Stdlib.print_int i;
                  Stdlib.print_newline ();
                  Result.return ValueUnit
                | _ -> Result.fail (TypeError (ValueInt 0))))
    |> set
         ~key:"print_endline"
         ~data:
           (ValueBuiltin
              (function
                | ValueString s ->
                  Stdlib.print_endline s;
                  Result.return ValueUnit
                | _ -> Result.fail (TypeError (ValueString ""))))
    |> set
         ~key:"print_bool"
         ~data:
           (ValueBuiltin
              (function
                | ValueBool b ->
                  Stdlib.print_string (string_of_bool b);
                  Stdlib.print_newline ();
                  Result.return ValueUnit
                | _ -> Result.fail (TypeError (ValueBool false))))
  ;;

  let rec check_match env = function
    | PatAny, _ -> Some env
    | PatConst (ConstInt i1), ValueInt i2 when i1 = i2 -> Some env
    | PatConst (ConstBool b1), ValueBool b2 when Bool.equal b1 b2 -> Some env
    | PatConst (ConstString s1), ValueString s2 when String.equal s1 s2 -> Some env
    | PatVariable x, v -> Some (extend env x v)
    | PatType (pat, _), v -> check_match env (pat, v)
    | PatTuple (p1, p2, pl), ValueTuple (v1, v2, vl) ->
      (match check_match env (p1, v1) with
       | None -> None
       | Some env1 ->
         (match check_match env1 (p2, v2) with
          | None -> None
          | Some env2 ->
            (match
               List.fold2 pl vl ~init:(Some env2) ~f:(fun acc_env p v ->
                 match acc_env with
                 | Some env' -> check_match env' (p, v)
                 | None -> None)
             with
             | Ok result -> result
             | Unequal_lengths -> None)))
    | _ -> None
  ;;

  let eval_binop (bop, v1, v2) =
    match bop, v1, v2 with
    | Multiply, ValueInt x, ValueInt y -> return (ValueInt (x * y))
    | Division, ValueInt _, ValueInt y when y = 0 -> fail DivisionByZeroError
    | Division, ValueInt x, ValueInt y -> return (ValueInt (x / y))
    | Plus, ValueInt x, ValueInt y -> return (ValueInt (x + y))
    | Minus, ValueInt x, ValueInt y -> return (ValueInt (x - y))
    | Equal, ValueInt x, ValueInt y -> return (ValueBool (x = y))
    | NotEqual, ValueInt x, ValueInt y -> return (ValueBool (x <> y))
    | LowerThan, ValueInt x, ValueInt y -> return (ValueBool (x < y))
    | LowestEqual, ValueInt x, ValueInt y -> return (ValueBool (x <= y))
    | GreaterThan, ValueInt x, ValueInt y -> return (ValueBool (x > y))
    | GretestEqual, ValueInt x, ValueInt y -> return (ValueBool (x >= y))
    | And, ValueBool x, ValueBool y -> return (ValueBool (x && y))
    | Or, ValueBool x, ValueBool y -> return (ValueBool (x || y))
    | _ -> fail (TypeError v1)
  ;;

  let eval_expr =
    let rec helper env = function
      | ExpConst c ->
        (match c with
         | ConstInt i -> return (ValueInt i)
         | ConstBool b -> return (ValueBool b)
         | ConstString s -> return (ValueString s)
         | ConstUnit -> return ValueUnit)
      | ExpIdent x ->
        let* v = find env x in
        let v =
          match v with
          | ValueClosure (p, true, e, env) -> ValueClosure (p, true, e, extend env x v)
          | _ -> v
        in
        return v
      | ExpBinOper (op, e1, e2) ->
        let* v1 = helper env e1 in
        let* v2 = helper env e2 in
        eval_binop (op, v1, v2)
      | ExpBranch (cond, then_expr, else_expr_opt) ->
        let* cond_value = helper env cond in
        (match cond_value with
         | ValueBool true -> helper env then_expr
         | ValueBool false ->
           (match else_expr_opt with
            | Some else_expr -> helper env else_expr
            | None -> return ValueUnit)
         | _ -> fail (TypeError cond_value))
      | ExpLet (is_rec, PatVariable x, expr1, expr2_opt) ->
        let* v = helper env expr1 in
        (match check_match env (PatVariable x, v) with
         | None -> fail PatternMatchingError
         | Some env1 ->
           let env2 =
             if is_rec
             then (
               match v with
               | ValueClosure (p, _, e, _) ->
                 let updated_closure = ValueClosure (p, true, e, env1) in
                 extend env1 x updated_closure
               | _ -> env1)
             else env1
           in
           (match expr2_opt with
            | Some expr2 -> helper env2 expr2
            | None -> return ValueUnit))
      | ExpLet (is_rec, PatType (pat, _), expr1, expr2_opt) ->
        let* v = helper env expr1 in
        (match check_match env (pat, v) with
         | None -> fail PatternMatchingError
         | Some env1 ->
           let env2 =
             if is_rec
             then (
               match v with
               | ValueClosure (p, _, e, _) ->
                 let updated_closure = ValueClosure (p, true, e, env1) in
                 extend
                   env1
                   (match pat with
                    | PatVariable x -> x
                    | _ -> "_")
                   updated_closure
               | _ -> env1)
             else env1
           in
           (match expr2_opt with
            | Some expr2 -> helper env2 expr2
            | None -> return ValueUnit))
      | ExpTuple (e1, e2, es) ->
        let* v1 = helper env e1 in
        let* v2 = helper env e2 in
        let* vs =
          List.fold_right es ~init:(return []) ~f:(fun e acc ->
            let* acc = acc in
            let* v = helper env e in
            return (v :: acc))
        in
        return (ValueTuple (v1, v2, vs))
      | ExpLambda (patterns, body) ->
        let rec create_nested_closures env patterns body =
          match patterns with
          | [] -> failwith "ExpLambda requires at least one pattern"
          | [ p ] -> ValueClosure (p, false, body, env)
          | p :: ps ->
            let inner_closure = create_nested_closures env ps body in
            ValueClosure (p, false, ExpLambda (ps, body), env)
        in
        return (create_nested_closures env patterns body)
      | ExpFunction (e1, e2) ->
        let* v1 = helper env e1 in
        let* v2 = helper env e2 in
        (match v1 with
         | ValueBuiltin f ->
           (match f v2 with
            | Ok result -> return result
            | Error e -> fail e)
         | ValueClosure (p, _, e, env) ->
           let* env' =
             match check_match env (p, v2) with
             | Some env -> return env
             | None -> fail PatternMatchingError
           in
           helper env' e
         | _ -> fail (TypeError v1))
      | _ -> fail NotImplemented
    in
    helper
  ;;

  let eval_str_item env = function
    | ExpLet (false, PatVariable x1, e1, None) ->
      let* v = eval_expr env e1 in
      let env = extend env x1 v in
      return env
    | ExpLet (true, PatVariable x1, e1, None) ->
      let* v = eval_expr env e1 in
      let env =
        match v with
        | ValueClosure (p, _, e, closure_env) ->
          let updated_closure = ValueClosure (p, true, e, extend closure_env x1 v) in
          extend env x1 updated_closure
        | _ -> extend env x1 v
      in
      return env
    | ExpLet (is_rec, PatType (pat, _), e1, Some body) ->
      let* v = eval_expr env e1 in
      (match check_match env (pat, v) with
       | None -> fail PatternMatchingError
       | Some env1 ->
         let env2 =
           if is_rec
           then (
             match v with
             | ValueClosure (p, _, e, _) ->
               let updated_closure = ValueClosure (p, true, e, env1) in
               extend
                 env1
                 (match pat with
                  | PatVariable x -> x
                  | _ -> "_")
                 updated_closure
             | _ -> env1)
           else env1
         in
         let* _ = eval_expr env2 body in
         return env2)
    | ExpLet (is_rec, PatVariable x1, e1, Some body) ->
      let* v = eval_expr env e1 in
      let env =
        if is_rec
        then (
          match v with
          | ValueClosure (p, _, e, closure_env) ->
            let updated_closure = ValueClosure (p, true, e, extend closure_env x1 v) in
            extend env x1 updated_closure
          | _ -> failwith "Expected a closure for recursive definition")
        else extend env x1 v
      in
      let* _ = eval_expr env body in
      return env
    | expr ->
      let* _ = eval_expr env expr in
      return env
    | _ -> fail NotImplemented
  ;;

  let eval_structure (s : program) =
    List.fold_left
      ~f:(fun env item ->
        let* env = env in
        let* env = eval_str_item env item in
        return env)
      ~init:(return initial_env)
      s
  ;;
end

module Inter = Eval (struct
    include Base.Result

    let ( let* ) m f = bind m ~f
  end)
