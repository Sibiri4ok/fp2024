(** Copyright 2024-2025, Danil Usoltsev *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Format

type ident = string [@@deriving show { with_path = false }]
type is_rec = bool [@@deriving show { with_path = false }]

type bin_oper =
  | Plus (* [+] *)
  | Minus (* [-] *)
  | Multiply (* [*] *)
  | Division (* [/] *)
  | And (* [&&] *)
  | Or (* [||] *)
  | GretestEqual (* [>=] *)
  | LowestEqual (* [<=] *)
  | GreaterThan (* [>] *)
  | LowerThan (* [<] *)
  | Equal (* [=] *)
  | NotEqual (* [<>] *)
  | Cons (* [::] *)
[@@deriving show { with_path = false }]

type unar_oper =
  | Negative (* [-x] *)
  | Not (* [not x]*)
  | Positive (* [+x] *)
[@@deriving show { with_path = false }]

type const =
  | ConstInt of int (* Integer constant: Example - [21] *)
  | ConstBool of bool (* Boolean constant: Example - [true] or [false] *)
  | ConstString of string (* String constant: Example - "I like OCaml!" *)
  | ConstUnit
[@@deriving show { with_path = false }]

type binder = int [@@deriving show { with_path = false }]

type ty =
  | TyVar of binder
  | TyPrim of string
  | TyArrow of ty * ty
  | TyList of ty
  | TyTuple of ty list
  | TyOption of ty
[@@deriving show { with_path = false }]

type pattern =
  | PatVariable of ident (* [x] *)
  | PatConst of const (* [21] or [true] or [false] *)
  | PatTuple of pattern * pattern * pattern list (* (x1; x2 ... xn) *)
  | PatAny
  (* | PatType of pattern * ty *)
  | PatUnit
  | PatList of pattern list
  | PatCons of pattern * pattern
  | PatOption of pattern option
[@@deriving show { with_path = false }]

type ty_pattern = pattern * ty option [@@deriving show { with_path = false }]

type expr =
  | ExpIdent of ident
  | ExpConst of const
  | ExpBranch of expr * expr * expr option
  | ExpTuple of expr * expr * expr list
  | ExpList of expr list
  | ExpBinOper of bin_oper * expr * expr
  | ExpMatch of expr * case * case list
  | ExpFunction of case * case list
  | ExpUnarOper of unar_oper * expr
  | ExpLet of is_rec * bind * bind list * expr
  | ExpApply of expr * expr
  | ExpOption of expr option
  | ExpLambda of ty_pattern list * expr
  | ExpConstrant of expr * ty
[@@deriving show { with_path = false }]

and bind = ExpValueBind of ty_pattern * expr [@@deriving show { with_path = false }]
and case = ExpCase of pattern * expr [@@deriving show { with_path = false }]

type structure =
  | SEval of expr
  | SValue of is_rec * bind * bind list
[@@deriving show { with_path = false }]

type program = structure list [@@deriving show { with_path = false }]

let rec pp_ty fmt = function
  | TyPrim x -> fprintf fmt "%s" x
  | TyVar x -> fprintf fmt "%s" @@ Char.escaped (Char.chr (x + 97))
  | TyArrow (l, r) ->
    (match l, r with
     | TyArrow _, _ -> fprintf fmt "(%a) -> %a" pp_ty l pp_ty r
     | _, _ -> fprintf fmt "%a -> %a" pp_ty l pp_ty r)
  | TyTuple tys ->
    (* Обновлено *)
    fprintf fmt "(%a)" (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " * ") pp_ty) tys
  | TyList ty ->
    (match ty with
     | TyArrow _ | TyTuple _ -> fprintf fmt "(%a) list" pp_ty ty
     | _ -> fprintf fmt "%a list" pp_ty ty)
  | TyOption ty ->
    (match ty with
     | TyArrow _ | TyTuple _ -> fprintf fmt "(%a) option" pp_ty ty
     | _ -> fprintf fmt "%a option" pp_ty ty)
;;
