(** Copyright 2024-2025, Danil Usoltsev *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type binder = int

module VarSet : Stdlib.Set.S with type elt = int

type ty =
  | TyVar of binder
  | TyPrim of string
  | TyArrow of ty * ty
  | TyTuple of ty list
  | TyList of ty
  | TyOption of ty

type scheme = Scheme of VarSet.t * ty

type error =
  | OccursCheck of int * ty
  | NoVariable of string
  | UnificationFailed of ty * ty
  | SeveralBounds of string
  | NotImplemented

val pp_ty : Format.formatter -> ty -> unit

val pp_error : Format.formatter -> error -> unit