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
let rec app f = function
  | [] -> raise MultiApplicationException
  | x::[] -> Application (f, x)
  | x::xs' -> app (Application (f, x)) xs'

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
    assert (t = (app tru [t; f] |> beta));
    assert (f = (app fls [t; f] |> beta))
  )

let and_ = abstr ["a"; "b"] (app (Variable "a") [Variable "b"; fls])
let or_ = abstr ["a"; "b"] (app (Variable "a") [tru; Variable "b"])

let () =
  assert (tru = (app and_ [tru; tru] |> beta));
  assert (fls = (app and_ [tru; fls] |> beta));
  assert (fls = (app and_ [fls; tru] |> beta));
  assert (fls = (app and_ [fls; fls] |> beta));

  assert (tru = (app or_ [tru; tru] |> beta));
  assert (tru = (app or_ [tru; fls] |> beta));
  assert (tru = (app or_ [fls; tru] |> beta));
  assert (fls = (app or_ [fls; fls] |> beta));
