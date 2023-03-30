namespace Parsimonious

module Kore =

  type Typ = O | Hom of Typ * Typ | B of Typ

  let rec showTyp (typ : Typ) : string =
    match typ with
    | O -> "o"
    | Hom (a, b) -> $"{go a} -> {go b}"
    | B a -> $"!{go a}"
  
  and private go typ =
    match typ with
    | O -> "o"
    | Hom (a, b) -> $"({go a} -> {go b})"
    | B a -> $"!{go a}"

  /// Terms of the simply typed very parsimonious lambda calculus.
  type Term =
    | Var of string
    | LamAff of string * Term
    | LamBox of string * Term
    | App of Term * Term
    | Box of Term
    | Let of string * Term * Term
    | Ann of Term * Typ
  
  let rec showTerm (trm : Term) =
    match trm with
    | Var x -> x
    | LamAff (x, t) -> $"λ{x}.{showTerm t}" 
    | LamBox (x, t) -> $"λ!{x}.{showTerm t}"
    | App (t, u) -> $"({showTerm t} {showTerm u})"
    | Box t -> $"!{showTerm t}"
    | Let (x, t, u) -> $"let {x} = {showTerm t}\{showTerm u}"
    | Ann (t, a) -> $"({showTerm t} : {showTyp a})"
  
  /// Values of terms of the simply typed very parsimonious lambda
  /// calculus. Used in defining semantics and evaluation.
  type Value =
    | VVar of string
    | VLamAff of Closure
    | VLamBox of Closure
    | VApp of Value * Value
    | VBox of Value
  
  and Env = (string * Value) list

  and [<Struct>] Closure =
    Closure of (string * struct (Env * Term))

  let rec lookup (env : Env) x =
    match env with
    | (y, v) :: _ when y = x -> ValueSome v
    | _ :: env -> lookup env x
    | [] -> ValueNone

  let rec fresh (env : Env) x =
    if x = "_" then x else
      match lookup env x with
      | ValueSome _ -> fresh env (x + "'")
      | ValueNone -> x

  let rec eval env trm =
    let inline mkClosure x env t = Closure (x, struct (env, t))
    let inline (@@) (Closure (x, struct (env, t))) u = eval ((x, u) :: env) t
    match trm with
    | Var x -> (lookup env x).Value
    | LamAff (x, t) -> VLamAff (mkClosure x env t)
    | LamBox (x, t) -> VLamBox (mkClosure x env t)
    | App (t, u) ->
      match eval env t, eval env u with
      | VLamAff xt, u -> xt @@ u
      | VLamBox xt, VBox u -> xt @@ u
      | t, u -> VApp (t, u)
    | Box t -> VBox (eval env t)
    | Let (x, t, u) -> eval ((x, eval env t) :: env) u
    | Ann (t, _) -> eval env t

  let inline (@@) (Closure (x, struct (env, t))) u = eval ((x, u) :: env) t
  
  let rec quote env v =
    match v with
    | VVar x -> Var x
    | VLamAff (Closure (x, _) as xt) ->
      let x = fresh env x
      let vx = VVar x
      LamAff (x, quote ((x, vx) :: env) (xt @@ vx))
    | VLamBox (Closure (x, _) as xt) ->
      let x = fresh env x
      let vx = VVar x
      LamBox (x, quote ((x, vx) :: env) (xt @@ vx))
    | VApp (t, u) -> App (quote env t, quote env u)
    | VBox t -> Box (quote env t)

  let showValueWith env v = showTerm (quote env v)
  
  let showValue v = showValueWith [] v

  /// Normalization by evaluation, with environment.
  let normalizeWith env t = quote env (eval env t)

  /// Normalization by evaluation.
  let normalize t = normalizeWith [] t

  type Usage = Lin of int | Exp of int | Used
  
  type Typing = { Name : string; mutable Usage : Usage; Typ : Typ }

  let rec getTyping (ctx : Typing list) x =
    match ctx with
    | ting :: _ when ting.Name = x -> ValueSome ting 
    | _ :: ctx -> getTyping ctx x
    | [] -> ValueNone

  /// Bidirectional type inference.
  let rec infer ctx dep (trm : Term) =
    match trm with
    | Var x ->
      match getTyping ctx x with
      | ValueSome ting ->
        match ting.Usage with
        | Lin d when d = dep -> ting.Usage <- Used; ting.Typ
        | Lin _ -> failwith $"Linear var {x} breaks depth restriction."
        | Exp d when d = dep -> ting.Typ
        | Exp d when d = dep - 1 -> ting.Usage <- Used; ting.Typ
        | Exp _ -> failwith $"Exponential var {x} breaks depth restriction."
        | Used -> failwith $"Var {x} breaks affine usage rules."
      | ValueNone -> failwith $"Untyped var {x}."
    | LamAff _ | LamBox _ -> failwith "Can't infer types of raw lambdas."
    | App (f, a) ->
      match infer ctx dep f with
      | Hom (d, c) -> check ctx dep a d; c
      | _ -> failwith $"Inferred non-function application in {trm}."
    | Box t -> B (infer ctx (dep + 1) t)
    | Ann (t, typ) -> check ctx dep t typ; typ
    | Let (x, t, u) ->
      let a = infer ctx dep t
      let xa = { Name = x; Usage = Lin dep; Typ = a }
      infer (xa :: ctx) dep u
  
  /// Bidirectional type checking.
  and check ctx dep trm typ =
    match trm with
    | LamAff (x, b) ->
      match typ with
      | Hom (c, d) ->
        let xc = { Name = x; Usage = Lin dep; Typ = c }
        check (xc :: ctx) dep b d
      | _ -> failwith $"Affine lambda can't have non-function type {typ}."
    | LamBox (x, b) ->
      match typ with
      | Hom (B c, d) ->
        let xc = { Name = x; Usage = Exp dep; Typ = c }
        check (xc :: ctx) dep b d
      | _ -> failwith $"Box-lambda can't have non-box-function type {typ}."
    | Box t ->
      match typ with
      | B ty -> check ctx (dep + 1) t ty
      | _ -> failwith $"Type mismatch, box {trm} cannot have non-box type {typ}."
    | _ ->
      let inf = infer ctx dep trm
      if inf <> typ then
        failwith $"Type mismatch, inferred {inf} instead of {typ}."
