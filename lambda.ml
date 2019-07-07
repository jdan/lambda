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

let and_ a b = app [a; b; fls]
let or_ a b = app [a; tru; b]
let not_ a = app [a; fls; tru]

let () =
  assert (tru = (and_ tru tru |> beta));
  assert (fls = (and_ tru fls |> beta));
  assert (fls = (and_ fls tru |> beta));
  assert (fls = (and_ fls fls |> beta));

  assert (tru = (or_ tru tru |> beta));
  assert (tru = (or_ tru fls |> beta));
  assert (tru = (or_ fls tru |> beta));
  assert (fls = (or_ fls fls |> beta));

  assert (fls = (not_ tru |> beta));
  assert (tru = (not_ fls |> beta))

(* List operations *)
let pair x y = Abstraction ("z", app [Variable "z"; x; y])
let first p = Application (p, tru)
let second p = Application(p, fls)

(* represent a list as a pair where the
 * head is whether the list is nil, and the
 * tail is the list itself
*)
let nil = pair tru tru
let isnil = first
let cons a b = pair fls (pair a b)
let head p = first (second p)
let tail p = second (second p)

let () =
  let ls = cons (Variable "a") (cons (Variable "b") (cons (Variable "c") nil))
  in (
    assert (Variable "a" = (head ls |> beta));
    assert (Variable "b" = (head (tail ls) |> beta));
    assert (Variable "c" = (head (tail (tail ls)) |> beta));
    assert (tru = (isnil (head (tail (tail (tail ls)))) |> beta));
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
let pred n = abstr ["f"; "x"] (
    let ux = Abstraction ("u", Variable "x")
    and uu = Abstraction ("u", Variable "u")
    and inner = abstr ["g"; "h"] (
        Application ( Variable "h"
                    , Application ( Variable "g"
                                  , Variable "f"
                                  )
                    )
      )
    in app [n; inner; ux; uu]
  )

let () =
  let two = succ (succ zero)
  and three = succ (succ (succ zero))
  and seven = succ (succ (succ (succ (succ (succ (succ zero))))))
  and pair' = abstr ["x"; "y"; "z"] (app [Variable "z"; Variable "x"; Variable "y"])
  in let cons' = abstr ["a"; "b"] (app [pair'; fls; app [pair'; Variable "a"; Variable "b"]])
  in let f = Abstraction ("p", app [cons'; Variable "#"; Variable "p"])
  in let rec len_of_lambda_list ls =
       if beta (isnil ls) = tru
       then 0
       else 1 + (len_of_lambda_list (tail ls))
  in (
    assert (0 = (app [zero; f; nil] |> len_of_lambda_list));
    assert (2 = (app [two; f; nil] |> len_of_lambda_list));
    assert (5 = (app [add two three; f; nil] |> len_of_lambda_list));
    assert (6 = (app [mult two three; f; nil] |> len_of_lambda_list));
    assert (48 = (app [pred (mult seven seven); f; nil] |> len_of_lambda_list));
  )
