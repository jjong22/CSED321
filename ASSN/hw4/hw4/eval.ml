(*
 * Call-by-value reduction   
 *)
open Uml

exception NotImplemented 
exception Stuck

let freshVarCounter = ref 0
                          
(*   getFreshVariable : string -> string 
 *   use this function if you need to generate a fresh variable from s. 
 *)
let getFreshVariable s = 
  let _ = freshVarCounter := !freshVarCounter + 1
  in
  s ^ "__" ^ (string_of_int (!freshVarCounter))
               
(*
 * implement a single step with reduction using the call-by-value strategy.
 *)

let isValue e = 
  match e with
  | Lam _ -> true (* lambda is a value *)
  | Var _ -> true 
  | App _ -> false
  | _ -> false

let rec subst e x v = 
  match e with
  | Var y -> if x = y then v else e (* no change *)
  | Lam (y, e1) -> 
    if x = y then Lam (y, e1) (* no change *)
    else 
      let y' = getFreshVariable y in (* generate a fresh variable *)
      let e1' = subst e1 y (Var y') in
      Lam (y', subst e1' x v)
  | App (e1, e2) -> App (subst e1 x v, subst e2 x v) (* subst in both e1 and e2 *)
  | _ -> raise NotImplemented


let rec stepv e =
  match e with
  | App (Lam (x, e1), v) when isValue v -> subst e1 x v (* App *)
  | App (v, e2) when isValue v -> (* Arg *)
    let e2' = stepv e2 in
    App (v, e2')
  | App (e1, e2) -> (* Lam *)
    let e1' = stepv e1 in
    App (e1', e2)
  | _ -> raise Stuck         

let stepOpt stepf e = try Some (stepf e) with Stuck -> None

let rec multiStep stepf e = try multiStep stepf (stepf e) with Stuck -> e

let stepStream stepf e =
  let rec steps e = 
    match (stepOpt stepf e) with 
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

