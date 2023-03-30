namespace Parsimonious

module Kore =

  let rec lookup (xks : (string * 'a) list) x =
    match xks with
    | (y, v) :: _ when y = x -> ValueSome v
    | _ :: xks -> lookup xks x
    | [] -> ValueNone

  /// Types of the simple typed very parsimonious lambda calculus.
  type Typ = O | Hom of Typ * Typ | B of Typ

  let showTyp (typ : Typ) : string =
    let inline paren p s = if p then $"({s})" else s
    let rec go p (typ : Typ) : string =
      match typ with
      | O -> "o"
      | Hom (a, b) -> paren p $"{go true a} -> {go true b}"
      | B a -> $"!{go true a}"
    go false typ

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

  let inline (@@) (Closure (x, struct (env, t))) u =
    eval ((x, u) :: env) t
  
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

  // TYPE SYSTEM

  type Usage = Lin of int | Exp of int | Used
  
  type Typing (usage : Usage, typ : Typ) =
    let mutable usage = usage
    member _.Usage = usage
    member _.Typ = typ
    member _.Use () = usage <- Used

  type Ctx = (string * Typing) list

  /// Bidirectional type inference.
  let rec infer (ctx : Ctx) dep (trm : Term) =
    match trm with
    | Var x ->
      match lookup ctx x with
      | ValueSome ting ->
        match ting.Usage with
        | Lin d when d = dep -> ting.Use (); ting.Typ
        | Lin _ -> failwith $"Linear var {x} breaks depth restriction."
        | Exp d when d = dep -> ting.Typ
        | Exp d when d = dep - 1 -> ting.Use (); ting.Typ
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
      let ting = Typing (Lin dep, a)
      infer ((x, ting) :: ctx) dep u
  
  /// Bidirectional type checking.
  and check ctx dep trm typ =
    match trm with
    | LamAff (x, b) ->
      match typ with
      | Hom (c, d) ->
        let ting = Typing (Lin dep, c)
        check ((x, ting) :: ctx) dep b d
      | _ -> failwith $"Affine lambda can't have non-function type {typ}."
    | LamBox (x, b) ->
      match typ with
      | Hom (B c, d) ->
        let ting = Typing (Exp dep, c)
        check ((x, ting) :: ctx) dep b d
      | _ -> failwith $"Box-lambda can't have non-box-function type {typ}."
    | Box t ->
      match typ with
      | B ty -> check ctx (dep + 1) t ty
      | _ -> failwith $"Type mismatch, box {trm} cannot have non-box type {typ}."
    | _ ->
      let inf = infer ctx dep trm
      if inf <> typ then
        failwith $"Type mismatch, inferred {inf} instead of {typ}."
