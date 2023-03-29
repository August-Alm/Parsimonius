namespace Parsimonious

module Program =

  open Kore

  let two =
    LamBox ("s", fun s ->
      LamAff ("z", fun z ->
        App (s, App (s, z))))

  let Nat a =
    Hom (B (Hom (a, a)), Hom (a, a))
  
  let f =
    LamBox ("x", fun x ->
      LamBox ("y", fun y ->
        Box (App (x, y))))
  
  let T =
    Hom (B (Hom (O, O)), Hom (B O, B O))
  
  let succ =
    LamAff ("n", fun n ->
      LamBox ("s", fun s ->
        LamAff ("z", fun z ->
          App (s, App (App (n, Box s), z)))))
  


  [<EntryPoint>]
  let main _ =
    check [] 0 two (Nat O)
    check [] 0 f T
    check [] 0 succ (Hom (Nat O, Nat O))
    let succAnn = Ann (succ, Hom (Nat O, Nat O))
    check [] 0 (App (succAnn, two)) (Nat O)
    let three = reduce (App (succ, two))
    printfn "%A" three
    0