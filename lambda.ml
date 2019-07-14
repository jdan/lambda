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
let succ n = abstr ["f"; "x"] (
    let nfx = app [n; Variable "f"; Variable "x"]
    in app [Variable "f"; nfx]
  )
let add m n = abstr ["f"; "x"] (
    let nfx = app [n; Variable "f"; Variable "x"]
    in app [m; Variable "f"; nfx]
  )
let mult m n = abstr ["f"; "x"] (
    app [ m
        ; app [n; Variable "f"]
        ; Variable "x"
        ]
  )
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

(* this isn't exactly right, "v" has to be carefully chosen *)
let minus a b = app [b; pred; a]
let iszero n = app [n; Abstraction ("x", fls); tru]

let () =
  let two = succ (succ zero)
  and three = succ (succ (succ zero))
  and seven = succ (succ (succ (succ (succ (succ (succ zero))))))
  in let rec int_of_church_encoding n =
       if tru = (iszero n |> beta)
       then 0
       else 1 + (int_of_church_encoding (opred n))
  in (
    assert (0 = (int_of_church_encoding zero));
    assert (2 = (int_of_church_encoding two));
    assert (5 = (add two three |> int_of_church_encoding));
    assert (6 = (mult two three |> int_of_church_encoding));
    assert (48 = (opred (mult seven seven) |> int_of_church_encoding));
    assert (4 = (minus seven three |> int_of_church_encoding));
  )

let rec js_of_term = function
  | Variable v -> v
  | Application (a, b) ->
    let a' = js_of_term a
    and b' = js_of_term b
    in "(" ^ a' ^ ")(" ^ b' ^ ")"
  | Abstraction (v, body) ->
    v ^ " => " ^ (js_of_term body)

(*
let () =
  (* let seven = succ (succ (succ (succ (succ (succ (succ zero)))))
   * in pred (mult seven seven) |> beta |> js_of_term |> print_endline;
   *)

  let js_0 = Variable "0"
  and js_1 = Variable "1"
  in let ls = cons js_0 (cons js_1 nil)
  in head (tail ls) |> js_of_term |> print_endline;
*)
