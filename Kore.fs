namespace Parsimonious

module Core =

  type Typ = O | Hom of Typ * Typ | B of Typ

  /// Terms of the simply typed very parsimonious lambda calculus.
  type Term =
    | Var of string
    | LamAff of string * Term
    | LamBox of string * Term
    | App of Term * Term
    | Box of Term
    | Let of string * Term * Term
    | Ann of Term * Typ
  
  type Value =
    | VVar of string
    | VLamAff of string * (Value -> Value)
    | VLamBox of string * (Value -> Value)
    | VApp of Value * Value
    | VBox of Value
  
  and Env = (string * Value) list

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
    match trm with
    | Var x -> (lookup env x).Value
    | LamAff (x, t) -> VLamAff (x, fun u -> eval ((x, u) :: env) t)
    | LamBox (x, t) -> VLamBox (x, fun u -> eval ((x, u) :: env) t)
    | App (t, u) ->
      match eval env t, eval env u with
      | VLamAff (_, t), u -> t u
      | VLamBox (_, t), VBox u -> t u
      | t, u -> VApp (t, u)
    | Box t -> VBox (eval env t)
    | Let (x, t, u) -> eval ((x, eval env t) :: env) u
    | Ann (t, _) -> eval env t

  let rec quote env v =
    match v with
    | VVar x -> Var x
    | VLamAff (x, t) ->
      let x = fresh env x
      let xv = VVar x
      LamAff (x, quote ((x, xv) :: env) (t xv))
    | VLamBox (x, t) ->
      let x = fresh env x
      let xv = VVar x
      LamBox (x, quote ((x, xv) :: env) (t xv))
    | VApp (t, u) -> App (quote env t, quote env u)
    | VBox t -> Box (quote env t)

  let normalizeWith env t = quote env (eval env t)

  let normalize t = normalizeWith [] t

  type Usage = Lin of int | Exp of int | Used
  
  type Typing = { Name : string; mutable Usage : Usage; Typ : Typ }

  let rec inline getTyping (ctx : Typing list) x =
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


module Kore =


  type Typ = O | Hom of Typ * Typ | B of Typ

  /// Terms of the simply typed very parsimonious lambda calculus.
  type Term =
    | Var of string
    | LamAff of string * (Term -> Term)
    | LamBox of string * (Term -> Term)
    | App of Term * Term
    | Box of Term
    | Ann of Term * Typ
  
  /// Weak head normal form reduction.
  let rec reduce t =
    match t with
    | App (f, a) ->
      match reduce f, a with
      | LamAff (_, b), a -> reduce (b a)
      | LamBox (_, b), Box a -> reduce (b a)
      | _ -> t
    | _ -> t
  
  type Usage = Lin of int | Exp of int | Used
  
  type Typing = { Name : string; mutable Usage : Usage; Typ : Typ }

  /// Bidirectional type inference.
  let rec infer ctx dep trm =
    match trm with
    | Var x ->
      match List.tryFind (fun ting -> ting.Name = x) ctx with
      | None -> failwith $"Untyped var {x}."
      | Some ting ->
        match ting.Usage with
        | Lin d when d = dep -> ting.Usage <- Used; ting.Typ
        | Lin _ -> failwith $"Linear var {x} breaks depth restriction."
        | Exp d when d = dep -> ting.Typ
        | Exp d when d = dep - 1 -> ting.Usage <- Used; ting.Typ
        | Exp _ -> failwith $"Exponential var {x} breaks depth restriction."
        | Used -> failwith $"Var {x} breaks affine usage rules."
    | LamAff _ | LamBox _ -> failwith "Can't infer types of raw lambdas."
    | App (f, a) ->
      match infer ctx dep f with
      | Hom (d, c) -> check ctx dep a d; c
      | _ -> failwith $"Inferred non-function application in {trm}."
    | Box t -> B (infer ctx (dep + 1) t)
    | Ann (t, typ) -> check ctx dep t typ; typ
  
  /// Bidirectional type checking.
  and check ctx dep trm typ =
    match trm with
    | LamAff (x, b) ->
      match typ with
      | Hom (c, d) ->
        let xc = { Name = x; Usage = Lin dep; Typ = c }
        check (xc :: ctx) dep (b (Var x)) d
      | _ -> failwith $"Affine lambda can't have non-function type {typ}."
    | LamBox (x, b) ->
      match typ with
      | Hom (B c, d) ->
        let xc = { Name = x; Usage = Exp dep; Typ = c }
        check (xc :: ctx) dep (b (Var x)) d
      | _ -> failwith $"Box-lambda can't have non-box-function type {typ}."
    | Box t ->
      match typ with
      | B ty -> check ctx (dep + 1) t ty
      | _ -> failwith $"Type mismatch, box {trm} cannot have non-box type {typ}."
    | _ ->
      let inf = infer ctx dep trm
      if inf <> typ then
        failwith $"Type mismatch, inferred {inf} instead of {typ}."