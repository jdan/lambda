type term =
  | Variable of string
  | Abstraction of string * term
  | Application of term * term

let rec string_of_term = function
  | Variable v -> v
  | Abstraction (v, body) -> "λ" ^ v ^ "." ^ (string_of_term body)
  | Application (a, b) ->
    "(" ^ (string_of_term a) ^ " " ^ (string_of_term b) ^ ")"

let rec abstr vs body = match vs with
  | [] -> body
  | v::[] -> Abstraction (v, body)
  | v::vs' -> Abstraction (v, abstr vs' body)

let tru = abstr ["x"; "y"] (Variable "x")
let fls = abstr ["x"; "y"] (Variable "y")

let () =
  assert ("λx.λy.x" = (string_of_term tru));
  assert ("λx.λy.y" = (string_of_term fls));

exception MultiApplicationException
let rec app = function
  | a::b::[] -> Application (a, b)
  | a::b::xs' -> app (Application (a, b) :: xs')
  | _ -> raise MultiApplicationException

(* An incomplete alpha substitution that does not
 * guard against variable captures.
 *
 * We'll be using combinators for most of our code,
 * so no worries here.
*)
let rec alpha a b = function
  | Variable v ->
    if v = a
    then b
    else Variable v
  | Application (e1, e2) ->
    Application
      ( alpha a b e1
      , alpha a b e2
      )
  | Abstraction (v, body) ->
    if v = a
    then Abstraction (v, body)
    else Abstraction (v, alpha a b body)

exception BetaReductionException
let rec beta = function
  | Variable v -> Variable v
  | Abstraction (v, body) -> Abstraction (v, body)
  | Application (e1, e2) -> (
      match (beta e1) with
      | Abstraction (v, body) ->
        let e2' = beta e2
        in alpha v e2' body |> beta
      | _ -> raise BetaReductionException
    )

let () =
  let t = Variable "#t"
  and f = Variable "#f"
  in (
    assert (t = (app [tru; t; f] |> beta));
    assert (f = (app [fls; t; f] |> beta))
  )

let and_ = abstr ["a"; "b"] (app [Variable "a"; Variable "b"; fls])
let oand a b = app [and_; a; b]
let or_ = abstr ["a"; "b"] (app [Variable "a"; tru; Variable "b"])
let oor a b = app [or_; a; b]
let not_ = abstr ["a"] (app [Variable "a"; fls; tru])
let onot a = app [not_; a]

let () =
  assert (tru = (oand tru tru |> beta));
  assert (fls = (oand tru fls |> beta));
  assert (fls = (oand fls tru |> beta));
  assert (fls = (oand fls fls |> beta));

  assert (tru = (oor tru tru |> beta));
  assert (tru = (oor tru fls |> beta));
  assert (tru = (oor fls tru |> beta));
  assert (fls = (oor fls fls |> beta));

  assert (fls = (onot tru |> beta));
  assert (tru = (onot fls |> beta))

(* List operations *)
let pair = abstr ["x"; "y"; "z"]
    (app [ Variable "z"
         ; Variable "x"
         ; Variable "y"
         ])
let opair x y = app [pair; x; y]
let first = abstr ["p"] (app [Variable "p"; tru])
let ofirst p = app [first; p]
let second = abstr ["p"] (app [Variable "p"; fls])
let osecond p = app [second; p]

(* represent a list as a pair where the
 * head is whether the list is nil, and the
 * tail is the list itself
*)
let nil = opair tru tru
let isnil = first
let oisnil = ofirst
(* todo: show that opair (Variable "a") is not a safe operation
 * and protect all ofn's from this
*)
let cons = abstr ["a"; "b"] (app [pair; fls; app [pair; Variable "a"; Variable "b"]])
let ocons a b = app [cons; a; b]
let head = abstr ["p"] (app [first; app [second; Variable "p"]])
let ohead p = app [head; p]
let tail = abstr ["p"] (app [second; app [second; Variable "p"]])
let otail p = app [tail; p]

let if_ = abstr ["x"; "y"; "z"] (app [Variable "x"; Variable "y"; Variable "z"])
let oif x y z = app [if_; x; y; z]

let () =
  (* let ls = ocons (Variable "a") (ocons (Variable "b") (ocons (Variable "c") nil)) => FAILS *)
  let ls = ocons (Variable "#a") (ocons (Variable "#b") (ocons (Variable "#c") nil))
  in (
    assert (Variable "#a" = (ohead ls |> beta));
    assert (Variable "#b" = (ohead (otail ls) |> beta));
    assert (Variable "#c" = (ohead (otail (otail ls)) |> beta));
    assert (tru = (oisnil (ohead (otail (otail (otail ls)))) |> beta));
  )

(* Church numerals *)
let zero = abstr ["f"; "x"] (Variable "x")
let succ = abstr ["n"; "f"; "x"] (
    let nfx = app [Variable "n"; Variable "f"; Variable "x"]
    in app [Variable "f"; nfx]
  )
let osucc n = app [succ; n]
(* apply `succ` m times to n *)
let add = abstr ["m"; "n"] (app [Variable "m"; succ; Variable "n"])
let oadd m n = app [add; m; n]
(* apply "add n" m times to 0 *)
let mult = abstr ["m"; "n"] (
    let addn = abstr ["m"] (app [Variable "n"; succ; Variable "m"])
    in app [Variable "m"; addn; zero]
  )
let omult m n = app [mult; m; n]
let pred = abstr ["n"; "f"; "x"] (
    let ux = Abstraction ("u", Variable "x")
    and uu = Abstraction ("u", Variable "u")
    and inner = abstr ["g"; "h"] (
        Application ( Variable "h"
                    , Application ( Variable "g"
                                  , Variable "f"
                                  )
                    )
      )
    in app [Variable "n"; inner; ux; uu]
  )
let opred n = app [pred; n]

(* apply `pred` b times to a *)
let minus = abstr ["a"; "b"] (app [Variable "b"; pred; Variable "a"])
let ominus a b = app [minus; a; b]

let iszero = abstr ["n"] (app [Variable "n"; Abstraction ("x", fls); tru])
let oiszero n = app [iszero; n]

let rec int_of_church_encoding n =
  if tru = (oiszero n |> beta)
  then 0
  else 1 + (int_of_church_encoding (opred n))

let rec church_encoding_of_int n =
  if n = 0
  then zero
  else osucc (church_encoding_of_int (n - 1))

let () =
  let two = osucc (osucc zero)
  and three = osucc (osucc (osucc zero))
  and seven = osucc (osucc (osucc (osucc (osucc (osucc (osucc zero))))))
  in (
    assert (0 = (int_of_church_encoding zero));
    assert (2 = (int_of_church_encoding two));
    assert (5 = (oadd two three |> int_of_church_encoding));
    assert (6 = (omult two three |> int_of_church_encoding));
    assert (48 = (opred (omult seven seven) |> int_of_church_encoding));
    assert (4 = (ominus seven three |> int_of_church_encoding));
  )

let y =
  let xfxx =
    Abstraction
      ( "x"
      , Application
          ( Variable "f"
          , Application (Variable "x", Variable "x")
          )
      )
  in Abstraction ("f", Application (xfxx, xfxx))

(* Our language is eager, so we'll need the Z-combinator *)
let z =
  let vxxv =
    Abstraction
      ( "v"
      , app [Variable "x"; Variable "x"; Variable "v"]
      )
  in let branch =
       Abstraction
         ( "x"
         , Application (Variable "f", vxxv)
         )
  in Abstraction
    ( "f"
    , Application (branch, branch)
    )

let fact =
  let inner = abstr ["fib"; "n"] (
      app
        (* might need an if thing *)
        [ oiszero (Variable "n")
        ; Abstraction
            (  "_"
            , osucc zero
            )
        ; Abstraction
            ( "_"
            , omult
                (Variable "n")
                (Application (Variable "fib", opred (Variable "n")))
            )
        ; Variable "_"
        ]
    )
  in app [z; inner]

let () =
  app [fact; church_encoding_of_int 5]
  |> string_of_term
  |> print_endline;

  app [fact; church_encoding_of_int 5]
  |> beta
  |> int_of_church_encoding
  |> string_of_int
  |> print_endline

let rec js_of_term = function
  | Variable v -> v
  | Application (a, b) ->
    let a' = js_of_term a
    and b' = js_of_term b
    in "(" ^ a' ^ ")(" ^ b' ^ ")"
  | Abstraction (v, body) ->
    v ^ " => " ^ (js_of_term body)
