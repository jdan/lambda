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
let or_ = abstr ["a"; "b"] (app [Variable "a"; tru; Variable "b"])
let not_ = abstr ["a"] (app [Variable "a"; fls; tru])

let () =
  assert (tru = (app [and_; tru; tru] |> beta));
  assert (fls = (app [and_; tru; fls] |> beta));
  assert (fls = (app [and_; fls; tru] |> beta));
  assert (fls = (app [and_; fls; fls] |> beta));

  assert (tru = (app [or_; tru; tru] |> beta));
  assert (tru = (app [or_; tru; fls] |> beta));
  assert (tru = (app [or_; fls; tru] |> beta));
  assert (fls = (app [or_; fls; fls] |> beta));

  assert (fls = (Application (not_, tru) |> beta));
  assert (tru = (Application (not_, fls) |> beta))

(* List operations *)
let pair = abstr ["x"; "y"; "z"] (app [Variable "z"; Variable "x"; Variable "y"])
let first = Abstraction ("p", Application (Variable "p", tru))
let second = Abstraction ("p", Application (Variable "p", fls))

(* represent a list as a pair where the
 * head is whether the list is nil, and the
 * tail is the list itself
 *)
let nil = app [pair; tru; tru]
let isnil = first
let cons = abstr ["h"; "t"]
    (app [ pair
         ; fls
         ; app [pair; Variable "h"; Variable "t"]
         ])
let head = Abstraction ("z", Application (first, (Application (second, Variable "z"))))
let tail = Abstraction ("z", Application (second, (Application (second, Variable "z"))))

let () =
  let ls = app [cons; Variable "a"; app [cons; Variable "b"; app [cons; Variable "c"; nil]]]
  in (
    assert (Variable "a" = (Application (head, ls) |> beta));
    assert (Variable "b" = (Application (head, Application (tail, ls)) |> beta));
    assert (Variable "c" = (Application (head, Application (tail, Application (tail, ls))) |> beta));
    assert (tru = (Application (isnil, Application (head, Application (tail, Application (tail, Application (tail, ls))))) |> beta));
  )
