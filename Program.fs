namespace Parsimonious

module Program =

  open Kore

  let two =
    LamBox ("s", LamAff ("z",
        App (Var "s", App (Var "s", Var "z"))))

  let Nat a =
    Hom (B (Hom (a, a)), Hom (a, a))
  
  let f =
    LamBox ("x", LamBox ("y",
        Box (App (Var "x", Var "y"))))
  
  let T =
    Hom (B (Hom (O, O)), Hom (B O, B O))
  
  let succ =
    LamAff ("n", LamBox ("s", LamAff ("z",
          App (Var "s", App (App (Var "n", Box (Var "s")), Var "z")))))

  [<EntryPoint>]
  let main _ =
    printfn "nat = %s" (showTyp (Nat O))
    check [] 0 two (Nat O)
    check [] 0 f T
    check [] 0 succ (Hom (Nat O, Nat O))
    let succAnn = Ann (succ, Hom (Nat O, Nat O))
    check [] 0 (App (succAnn, two)) (Nat O)
    let three = normalize (App (succ, two))
    printfn "three = %s" (showTerm three)
    0