open Tml

exception TypeError

(***************************************************** 
 * replace unit by your own type for typing contexts *
 *****************************************************)
type context = Tml.var -> Tml.tp

(*
 * For each function you introduce, 
 * write its type, specification, and invariant. 
 *)

let createEmptyContext () = 
  fun x -> raise TypeError

(* val typing : context -> Tml.exp -> Tml.tp *)
(*cxt: contex, e: Tml.exp*)
let rec typing cxt e =
  match e with
  | Tml.Var x -> cxt x
  | Tml.Lam (v, tp, e) -> 
      let cxt' = fun x -> if x = v then tp else cxt x in
      let tp' = typing cxt' e in
      Tml.Fun (tp, tp')
  | Tml.App (e1, e2) ->
      let tp1 = typing cxt e1 in
      let tp2 = typing cxt e2 in
      (match tp1 with
       | Tml.Fun (tp11, tp12) when tp11 = tp2 -> tp12
       | _ -> raise TypeError)
  | Tml.Pair (e1, e2) ->
      let tp1 = typing cxt e1 in
      let tp2 = typing cxt e2 in
      Tml.Prod (tp1, tp2)
  | Tml.Fst e' ->
      let tp = typing cxt e' in
      (match tp with
       | Tml.Prod (tp1, _) -> tp1
       | _ -> raise TypeError)
  | Tml.Snd e' ->
      let tp = typing cxt e' in
      (match tp with
       | Tml.Prod (_, tp2) -> tp2
       | _ -> raise TypeError)
  | Tml.Eunit -> Tml.Unit
  | Tml.Inl (e', tp) ->
      let tp' = typing cxt e' in
      if tp = tp' then Tml.Sum (tp, tp) else raise TypeError
  | Tml.Inr (e', tp) ->
      let tp' = typing cxt e' in
      if tp = tp' then Tml.Sum (tp, tp) else raise TypeError
  | Tml.Case (e', v1, e1, v2, e2) ->
      let tp1 = typing cxt e' in
      let tp2 = typing (fun x -> if x = v1 then tp1 else cxt x) e1 in
      let tp3 = typing (fun x -> if x = v2 then tp1 else cxt x) e2 in
      (match tp1 with
       | Tml.Sum (tp11, tp12) when tp2 = tp11 && tp3 = tp12 -> tp2
       | _ -> raise TypeError)
  | Tml.Fix (v, tp, e) ->
      let cxt' = fun x -> if x = v then tp else cxt x in
      let tp' = typing cxt' e in
      if tp = tp' then tp else raise TypeError
  | Tml.True -> Tml.Bool
  | Tml.False -> Tml.Bool
  | Tml.Ifthenelse (e1, e2, e3) ->
      let tp1 = typing cxt e1 in
      let tp2 = typing cxt e2 in
      let tp3 = typing cxt e3 in
      if tp1 = Tml.Bool && tp2 = tp3 then tp2 else raise TypeError
  | Tml.Num _ -> Tml.Int
  | Tml.Plus -> Tml.Fun (Tml.Prod (Tml.Int, Tml.Int), Tml.Int)
  | Tml.Minus -> Tml.Fun (Tml.Prod (Tml.Int, Tml.Int), Tml.Int)
  | Tml.Eq -> Tml.Fun (Tml.Prod (Tml.Int, Tml.Int), Tml.Bool)
  | _ -> raise TypeError
  
let typeOf e = typing (createEmptyContext ()) e 
let typeOpt e = try Some (typeOf e) 
                with TypeError -> None



