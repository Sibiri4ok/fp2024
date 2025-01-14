(** Copyright 2024-2025, Danil Usoltsev *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

(* Template: https://gitlab.com/Kakadu/fp2020course-materials/-/tree/master/code/miniml?ref_type=heads*)

open Typing
open Base
open Ast

module VarSet = struct
  include Stdlib.Set.Make (Int)
end

module Result : sig
  type 'a t

  val bind : 'a t -> f:('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
  val fail : error -> 'a t

  include Monad.Infix with type 'a t := 'a t

  module Syntax : sig
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end

  (** Creation of a fresh name from internal state *)
  val fresh : int t

  (** Running a transformer: getting the inner result value *)
  val run : 'a t -> ('a, error) Result.t

  module RMap : sig
    val fold : ('a, 'b, 'c) Map.t -> init:'d t -> f:('a -> 'b -> 'd -> 'd t) -> 'd t
  end
end = struct
  (** A composition: State monad after Result monad *)
  type 'a t = int -> int * ('a, error) Result.t

  let ( >>= ) : 'a 'b. 'a t -> ('a -> 'b t) -> 'b t =
    fun m f st ->
    let last, r = m st in
    match r with
    | Result.Error x -> last, Result.fail x
    | Result.Ok a -> f a last
  ;;

  let fail e st = st, Result.fail e
  let return x last = last, Result.return x
  let bind x ~f = x >>= f

  let ( >>| ) : 'a 'b. 'a t -> ('a -> 'b) -> 'b t =
    fun m f st ->
    match m st with
    | st, Ok x -> st, Result.return (f x)
    | st, Result.Error e -> st, Result.fail e
  ;;

  module Syntax = struct
    let ( let* ) x f = bind x ~f
  end

  let fresh : int t = fun last -> last + 1, Result.return last
  let run m = snd (m 0)

  module RMap = struct
    let fold m ~init ~f =
      Map.fold m ~init ~f:(fun ~key ~data acc ->
        let open Syntax in
        let* acc = acc in
        f key data acc)
    ;;
  end
end

module Type = struct
  let rec occurs_in v = function
    | TyVar b -> b = v
    | TyArrow (l, r) -> occurs_in v l || occurs_in v r
    | TyTuple tl -> List.exists tl ~f:(occurs_in v)
    | TyList ty -> occurs_in v ty
    | TyOption t -> occurs_in v t
    | TyPrim _ -> false
  ;;

  let free_vars =
    let rec helper acc = function
      | TyVar b -> VarSet.add b acc
      | TyArrow (l, r) -> helper (helper acc l) r
      | TyTuple tl -> List.fold_left tl ~init:acc ~f:helper
      | TyList t -> helper acc t
      | TyPrim _ -> acc
    in
    helper VarSet.empty
  ;;
end

module Subst : sig
  type t

  val empty : t
  val singleton : int -> ty -> t Result.t
  val find : t -> int -> ty option
  val remove : t -> int -> t
  val apply : t -> ty -> ty
  val unify : ty -> ty -> t Result.t
  val compose : t -> t -> t Result.t
  val compose_all : t list -> t Result.t
end = struct
  open Result
  open Result.Syntax

  type t = (int, ty, Int.comparator_witness) Map.t

  let empty = Map.empty (module Int)
  let mapping k v = if Type.occurs_in k v then fail (OccursCheck (k, v)) else return (k, v)

  let singleton k v =
    let* k, v = mapping k v in
    return (Map.singleton (module Int) k v)
  ;;

  let find s k = Map.find s k
  let remove s k = Map.remove s k

  let apply s =
    let rec helper = function
      | TyPrim x -> TyPrim x
      | TyVar b as ty ->
        (match find s b with
         | None -> ty
         | Some x -> x)
      | TyArrow (l, r) -> TyArrow (helper l, helper r)
      | TyList t -> TyList (helper t)
      | TyTuple ts -> TyTuple (List.map ~f:helper ts)
    in
    helper
  ;;

  let rec unify l r =
    match l, r with
    | TyPrim l, TyPrim r when String.equal l r -> return empty
    | TyPrim _, TyPrim _ -> fail (UnificationFailed (l, r))
    | TyVar l, TyVar r when l = r -> return empty
    | TyVar b, t | t, TyVar b -> singleton b t
    | TyArrow (l1, r1), TyArrow (l2, r2) ->
      let* subs1 = unify l1 l2 in
      let* subs2 = unify (apply subs1 r1) (apply subs1 r2) in
      compose subs1 subs2
    | TyTuple ts1, TyTuple ts2 ->
      if List.length ts1 <> List.length ts2
      then fail (UnificationFailed (l, r))
      else (
        let rec unify_tuples subs ts1 ts2 =
          match ts1, ts2 with
          | [], [] -> return subs
          | t1 :: rest1, t2 :: rest2 ->
            let* subs' = unify (apply subs t1) (apply subs t2) in
            let* composed_subs = compose subs subs' in
            unify_tuples composed_subs rest1 rest2
          | _, _ -> failwith "This should not happen"
        in
        unify_tuples empty ts1 ts2)
    | TyList t1, TyList t2 -> unify t1 t2
    | TyOption t1, TyOption t2 -> unify t1 t2
    | _ -> fail (UnificationFailed (l, r))

  and extend k v s =
    match find s k with
    | None ->
      let v = apply s v in
      let* s2 = singleton k v in
      RMap.fold s ~init:(return s2) ~f:(fun k v acc ->
        let v = apply s2 v in
        let* k, v = mapping k v in
        return (Map.update acc k ~f:(fun _ -> v)))
    | Some v2 ->
      let* s2 = unify v v2 in
      compose s s2

  and compose s1 s2 = RMap.fold s2 ~init:(return s1) ~f:extend

  let compose_all =
    List.fold_left ~init:(return empty) ~f:(fun acc s ->
      let* acc = acc in
      compose acc s)
  ;;
end

module Scheme = struct
  type t = S of VarSet.t * ty

  let occurs_in v (S (xs, t)) = (not (VarSet.mem v xs)) && Type.occurs_in v t
  let free_vars (S (xs, t)) = VarSet.diff (Type.free_vars t) xs

  let apply s (S (set, tp)) =
    let s2 = VarSet.fold (fun k s -> Subst.remove s k) set s in
    S (set, Subst.apply s2 tp)
  ;;
end

module TypeEnv = struct
  type t = (ident, Scheme.t, String.comparator_witness) Map.t

  let extend e k v = Map.update e k ~f:(fun _ -> v)
  let remove e k = Map.remove e k
  let empty = Map.empty (module String)

  let free_vars : t -> VarSet.t =
    Map.fold ~init:VarSet.empty ~f:(fun ~key:_ ~data:s acc ->
      VarSet.union acc (Scheme.free_vars s))
  ;;

  let apply s env = Map.map env ~f:(Scheme.apply s)
  let find x env = Map.find env x
end

open Result
open Result.Syntax

let fresh_var = fresh >>| fun n -> TyVar n

let instantiate : Scheme.t -> ty Result.t =
  fun (S (xs, ty)) ->
  VarSet.fold
    (fun name typ ->
      let* typ = typ in
      let* f1 = fresh_var in
      let* s = Subst.singleton name f1 in
      return (Subst.apply s typ))
    xs
    (return ty)
;;

let generalize env ty =
  let free = VarSet.diff (Type.free_vars ty) (TypeEnv.free_vars env) in
  Scheme.S (free, ty)
;;

let generalize_rec env ty x =
  let env = TypeEnv.remove env x in
  generalize env ty
;;

let infer_const = function
  | ConstInt _ -> TyPrim "int"
  | ConstBool _ -> TyPrim "bool"
  | ConstString _ -> TyPrim "string"
;;

let rec infer_pattern env = function
  | PatAny ->
    let* fresh = fresh_var in
    return (env, fresh)
  | PatConst c -> return (env, infer_const c)
  | PatVariable x ->
    let* fresh = fresh_var in
    let env = TypeEnv.extend env x (Scheme.S (VarSet.empty, fresh)) in
    return (env, fresh)
  | PatTuple (p1, p2, pl) ->
    let* env, tl =
      List.fold_left
        ~f:(fun acc pat ->
          let* env1, tl = acc in
          let* env2, t = infer_pattern env1 pat in
          return (env2, t :: tl))
        ~init:(return (env, []))
        (p1 :: p2 :: pl)
    in
    return (env, TyTuple (List.rev tl))
  | PatType (pat, an) ->
    let* env1, t1 = infer_pattern env pat in
    let* sub = Subst.unify t1 an in
    let env = TypeEnv.apply sub env1 in
    return (env, Subst.apply sub t1)
;;

let infer_binop_type = function
  | Equal | NotEqual | GreaterThan | GretestEqual | LowerThan | LowestEqual ->
    fresh_var >>| fun fv -> fv, fv, TyPrim "bool"
  | Plus | Minus | Multiply | Division -> return (TyPrim "int", TyPrim "int", TyPrim "int")
  | And | Or -> return (TyPrim "bool", TyPrim "bool", TyPrim "bool")
;;

let infer_expr =
  let rec helper env = function
    | ExpConst c -> return (Subst.empty, infer_const c)
    | ExpIdent x ->
      (match TypeEnv.find x env with
       | Some s ->
         let* t = instantiate s in
         return (Subst.empty, t)
       | None -> fail (NoVariable x))
    | ExpBinOper (op, e1, e2) ->
      let* sub1, t1 = helper env e1 in
      let* sub2, t2 = helper (TypeEnv.apply sub1 env) e2 in
      let* e1t, e2t, et = infer_binop_type op in
      let* sub3 = Subst.unify (Subst.apply sub2 t1) e1t in
      let* sub4 = Subst.unify (Subst.apply sub3 t2) e2t in
      let* sub = Subst.compose_all [ sub1; sub2; sub3; sub4 ] in
      return (sub, Subst.apply sub et)
    | ExpBranch (i, t, e) ->
      let* sub1, t1 = helper env i in
      let* sub2, t2 = helper (TypeEnv.apply sub1 env) t in
      let* sub3, t3 =
        match e with
        | Some e -> helper (TypeEnv.apply sub2 env) e
        | None -> return (Subst.empty, TyPrim "unit")
      in
      let* sub4 = Subst.unify t1 (TyPrim "bool") in
      let* sub5 = Subst.unify t2 t3 in
      let* sub = Subst.compose_all [ sub1; sub2; sub3; sub4; sub5 ] in
      return (sub, Subst.apply sub t2)
    | ExpTuple (e1, e2, el) ->
      let* sub, t =
        List.fold_left
          ~f:(fun acc e ->
            let* sub, t = acc in
            let* sub1, t1 = helper env e in
            let* sub2 = Subst.compose sub sub1 in
            return (sub2, t1 :: t))
          ~init:(return (Subst.empty, []))
          (e1 :: e2 :: el)
      in
      return (sub, TyTuple (List.rev_map ~f:(Subst.apply sub) t))
    | ExpList exprs ->
      (match exprs with
       | [] ->
         let* fresh = fresh_var in
         return (Subst.empty, TyList fresh)
       | hd :: tl ->
         let* sub1, ty_hd = helper env hd in
         let* sub, ty =
           List.fold_left
             ~f:(fun acc expr ->
               let* sub_acc, ty_acc = acc in
               let* sub_cur, ty_cur = helper env expr in
               let* sub_unify = Subst.unify ty_acc ty_cur in
               let* sub_combined = Subst.compose_all [ sub_acc; sub_cur; sub_unify ] in
               return (sub_combined, Subst.apply sub_combined ty_acc))
             ~init:(return (sub1, ty_hd))
             tl
         in
         return (sub, TyList ty))
    | ExpOption opt_expr ->
      (match opt_expr with
       | Some expr ->
         let* sub, ty = helper env expr in
         return (sub, TyOption ty)
       | None ->
         let* fresh_ty = fresh_var in
         return (Subst.empty, TyOption fresh_ty))
    | ExpFunction (e1, e2) ->
      let* fresh = fresh_var in
      let* s1, t1 = helper env e1 in
      let* s2, t2 = helper (TypeEnv.apply s1 env) e2 in
      let* s3 = Subst.unify (TyArrow (t2, fresh)) (Subst.apply s2 t1) in
      let* sub = Subst.compose_all [ s1; s2; s3 ] in
      let t = Subst.apply sub fresh in
      return (sub, t)
    | ExpLet (false, PatVariable x, e1, e2_opt) ->
      let* s1, t1 = helper env e1 in
      let env = TypeEnv.apply s1 env in
      let s = generalize env t1 in
      let env = TypeEnv.extend env x s in
      (match e2_opt with
       | None -> return (s1, t1)
       | Some e2 ->
         let* s2, t2 = helper env e2 in
         let* s = Subst.compose s1 s2 in
         return (s, t2))
    | ExpLet (true, PatVariable x, e1, e2_opt) ->
      let* fresh = fresh_var in
      let env1 = TypeEnv.extend env x (S (VarSet.empty, fresh)) in
      let* s, t = helper env1 e1 in
      let* s1 = Subst.unify t fresh in
      let* s2 = Subst.compose s s1 in
      let env = TypeEnv.apply s2 env in
      let t = Subst.apply s2 t in
      let scheme = generalize_rec env t x in
      let env = TypeEnv.extend env x scheme in
      (match e2_opt with
       | None -> return (s2, t)
       | Some e2 ->
         let* sub, t2 = helper env e2 in
         let* sub = Subst.compose s2 sub in
         return (sub, t2))
    | ExpLet (is_rec, PatType (pat, an), e1, e2_opt) ->
      let* env1, t1 = infer_pattern env pat in
      let* sub = Subst.unify t1 an in
      let env = TypeEnv.apply sub env1 in
      let* s1, t1 = helper env e1 in
      let env = TypeEnv.apply s1 env in
      let s = generalize env t1 in
      let env =
        TypeEnv.extend
          env
          (match pat with
           | PatVariable x -> x
           | _ -> "_")
          s
      in
      (match e2_opt with
       | None -> return (s1, t1)
       | Some e2 ->
         let* s2, t2 = helper env e2 in
         let* s = Subst.compose s1 s2 in
         return (s, t2))
    | ExpLambda (patterns, body) ->
      let init_env = return (env, Subst.empty, []) in
      let* env', sub_patterns, param_types =
        List.fold_left
          ~f:(fun acc pattern ->
            let* env_acc, sub_acc, types_acc = acc in
            let* env_updated, param_type = infer_pattern env_acc pattern in
            return (env_updated, sub_acc, param_type :: types_acc))
          ~init:init_env
          patterns
      in
      let param_types = List.rev param_types in
      let* sub_body, body_type = helper env' body in
      let* sub = Subst.compose_all [ sub_patterns; sub_body ] in
      let tarrow l r = TyArrow (l, r) in
      let function_type = List.fold_right param_types ~init:body_type ~f:tarrow in
      return (sub, function_type)
    | _ -> fail NotImplemented
  in
  helper
;;

let rec infer_structure_item env = function
  | ExpLet (true, PatVariable x1, e1, None) ->
    (* Рекурсивное объявление *)
    let* fresh = fresh_var in
    let sc = Scheme.S (VarSet.empty, fresh) in
    let env = TypeEnv.extend env x1 sc in
    let* s1, t1 = infer_expr env e1 in
    let* s2 = Subst.unify t1 fresh in
    let* s3 = Subst.compose s1 s2 in
    let env = TypeEnv.apply s3 env in
    let t2 = Subst.apply s3 t1 in
    let sc = generalize_rec env t2 x1 in
    let env = TypeEnv.extend env x1 sc in
    return env
  | ExpLet (false, PatVariable x1, e1, None) ->
    (* Нерекурсивное объявление *)
    let* s, t = infer_expr env e1 in
    let env = TypeEnv.apply s env in
    let sc = generalize env t in
    let env = TypeEnv.extend env x1 sc in
    return env
  | ExpLet (is_rec, PatType (pat, an), e1, e2_opt) ->
    (* Объявление с аннотированным типом *)
    let* env1, t1 = infer_pattern env pat in
    let* sub = Subst.unify t1 an in
    let env = TypeEnv.apply sub env1 in
    let* s1, t1 = infer_expr env e1 in
    let env = TypeEnv.apply s1 env in
    let s = generalize env t1 in
    let env =
      TypeEnv.extend
        env
        (match pat with
         | PatVariable x -> x
         | _ -> "_")
        s
    in
    (match e2_opt with
     | None -> return env
     | Some e2 ->
       let* s2, t2 = infer_expr env e2 in
       let* s = Subst.compose s1 s2 in
       return (TypeEnv.apply s env))
  | ExpLet (is_rec, PatVariable x1, e1, Some body) ->
    (* Объявление с телом *)
    let* env = infer_structure_item env (ExpLet (is_rec, PatVariable x1, e1, None)) in
    infer_expr env body >>= fun _ -> return env
  | expr ->
    (* Обработка остальных выражений *)
    let* s, t = infer_expr env expr in
    return (TypeEnv.extend env "_" (Scheme.S (VarSet.empty, t)))
;;

let infer_structure (structure : program) =
  let rec process_items env items =
    match items with
    | [] -> return env
    | ExpLet (is_rec, pattern, expr, None) :: rest ->
      let* env = infer_structure_item env (ExpLet (is_rec, pattern, expr, None)) in
      process_items env rest
    | ExpLet (is_rec, pattern, expr, Some body) :: rest ->
      let* env = infer_structure_item env (ExpLet (is_rec, pattern, expr, Some body)) in
      process_items env rest
    | expr :: rest ->
      let* env = infer_structure_item env expr in
      process_items env rest
  in
  process_items TypeEnv.empty structure
;;

let run_infer s = run (infer_structure s)
