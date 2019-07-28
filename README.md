## lambda

The (incomplete) [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus), in OCaml

```ocaml
let () =
  app [fact; church_encoding_of_int 5]
  |> string_of_term
  |> print_endline;
  (* ((λf.(λx.(f λv.((x x) v)) λx.(f λv.((x x) v))) λfib.λn
     .((((λn.((n λx.λx.λy.y) λx.λy.x) n) λ_.(λn.λf.λx.(f ((
     n f) x)) λf.λx.x)) λ_.((λm.λn.((m λm.((n λn.λf.λx.(f (
     (n f) x))) m)) λf.λx.x) n) (fib (λn.λf.λx.(((n λg.λh.(
     h (g f))) λu.x) λu.u) n)))) λx.x)) λf.λx.(f (f (f (f (
     f x))))))
  *)

  app [fact; church_encoding_of_int 5]
  |> beta
  |> int_of_church_encoding
  |> string_of_int
  |> print_endline;
  (* 120 *)

  app [fact; church_encoding_of_int 5]
  |> js_of_term
  |> print_endline;
  (* ((f => (x => (f)(v => ((x)(x))(v)))(x => (f)(v => ((x)(
     x))(v))))(fib => n => ((((n => ((n)(x => x => y => y))(
     x => y => x))(n))(_ => (n => f => x => (f)(((n)(f))(x))
     )(f => x => x)))(_ => ((m => n => ((m)(m => ((n)(n =>
     f => x => (f)(((n)(f))(x))))(m)))(f => x => x))(n))((fib)
     ((n => f => x => (((n)(g => h => (h)((g)(f))))(u => x))
     (u => u))(n)))))(x => x)))(f => x => (f)((f)((f)((f)((f
     )(x))))))

     (n => n + 1)(0)  // call with an increment and 0 to get a num
  *)
```
