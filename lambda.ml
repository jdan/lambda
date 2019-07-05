type term =
  | Variable of string
  | Abstraction of string * term
  | Application of term * term

let rec string_of_term = function
  | Variable v -> v
  | Abstraction (v, body) -> "λ" ^ v ^ "." ^ (string_of_term body)
  | Application (a, b) ->
    "(" ^ (string_of_term a) ^ " " ^ (string_of_term b) ^ ")"

let rec multi_abstr vs body = match vs with
  | [] -> body
  | v::[] -> Abstraction (v, body)
  | v::vs' -> Abstraction (v, multi_abstr vs' body)

let tru = multi_abstr ["x"; "y"] (Variable "x")
let fls = multi_abstr ["x"; "y"] (Variable "y")

let () =
  assert ("λx.λy.x" = (string_of_term tru));
  assert ("λx.λy.y" = (string_of_term fls));

exception MultiApplicationException
let rec multi_app f = function
  | [] -> raise MultiApplicationException
  | x::[] -> Application (f, x)
  | x::xs' -> multi_app (Application (f, x)) xs'

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
        in alpha v e2' body
    | _ -> raise BetaReductionException
  )

let () =
  let t = Variable "#t"
  and f = Variable "#f"
  in
    assert (t = (multi_app tru [t; f] |> beta));
    assert (f = (multi_app fls [t; f] |> beta));

