open Tml
exception NotImplemented 
exception Stuck
exception NotConvertible

type stoval = 
    Computed of value 
  | Delayed of exp * env

 and stack =
   Hole_SK
   | Frame_SK of stack * frame

 and state =
   Anal_ST of (stoval Heap.heap) * stack * exp * env
   | Return_ST of (stoval Heap.heap) * stack * value 

 (* Define your own datatypes *)
 and env = index -> int (*exp -> int ?*)
 
 and value =
  | Indv of index
  | Lamv of exp
  | Appv of exp * exp
  | Pairv of exp * exp
  | Fstv of exp
  | Sndv of exp
  | Eunitv
  | Inlv of exp
  | Inrv of exp
  | Casev of exp * exp * exp
  | Truev
  | Falsev
  | Ifthenelsev of exp * exp * exp
  | Numv of int
  | Plusv
  | Minusv
  | Eqv

 and frame = Hole_F | Value_F of value | Exp_F of exp
  | Lam_F of frame
  | App_F of frame * exp
  | App_F' of exp * frame
  | Pair_F of frame * exp
  | Pair_F' of exp * frame
  | Fst_F of frame
  | Snd_F of frame
  | Inl_F of frame
  | Inr_F of frame
  | Case_F of frame * exp * exp
  | Ifthenelse_F of frame * exp * exp
  | Fix_F of frame
  
(* Define your own empty environment *)
let emptyEnv = fun exp -> 0

(* Implement the function value2exp : value -> Tml.exp
 * Warning : If you give wrong implementation of this function,
 *           you wiil receive no credit for the entire third part!  *)
let value2exp v =
  match v with
  | Indv i -> Ind i
  | Lamv e -> Lam e
  | Appv (e1, e2) -> App (e1, e2)
  | Pairv (e1, e2) -> Pair (e1, e2)
  | Fstv e -> Fst e
  | Sndv e -> Snd e
  | Eunitv -> Eunit
  | Inlv e -> Inl e
  | Inrv e -> Inr e
  | Casev (e, e1, e2) -> Case (e, e1, e2)
  | Truev -> True
  | Falsev -> False
  | Ifthenelsev (e, e1, e2) -> Ifthenelse (e, e1, e2)
  | Numv int -> Num int
  | Plusv -> Plus
  | Minusv -> Minus
  | Eqv -> Eq

(*helper function*)
let exp2value v =
  match v with
  | Ind x -> Indv x
  | Lam e -> Lamv e
  | App (e1, e2) -> Appv (e1, e2)
  | Pair (e1, e2) -> Pairv (e1, e2)
  | Fst e -> Fstv e
  | Snd e -> Sndv e
  | Eunit -> Eunitv
  | Inl e -> Inlv e
  | Inr e -> Inrv e
  | Case (e, e1, e2) -> Casev (e, e1, e2)
  | True -> Truev
  | False -> Falsev
  | Ifthenelse (e, e1, e2) -> Ifthenelsev (e, e1, e2)
  | Num n -> Numv n
  | Plus -> Plusv
  | Minus -> Minusv
  | Eq -> Eqv
  | _ -> raise Stuck

(* Problem 1. 
 * texp2exp : Tml.texp -> Tml.exp *)
let texp2exp txp =
  let rec aux txp fn = 
    match txp with
      | Tvar var -> fun x -> if fn x < fn "_" || x = var then fn x else if fn var = fn "_" then (fn x) + 1 else fn x
      | Tlam (var, tp, texp) -> 
        fun x -> if fn x < fn "_" then fn x 
                 else if x = var then (aux texp (fun x -> if x = var then -1 else fn x)) "_"
                 else ((aux texp (fun x -> if x = var then -1 else fn x)) x)
      | Tapp (texp1, texp2) -> aux texp1 (aux texp2 fn)
      | Tpair (texp1, texp2) -> aux texp1 (aux texp2 fn)
      | Tfst texp -> aux texp fn
      | Tsnd texp -> aux texp fn
      | Tinl (texp, tp) -> aux texp fn
      | Tinr (texp, tp) -> aux texp fn
      | Tcase (texp, var1, texp1, var2, texp2) ->
        aux texp (aux (Tlam(var1, Int, texp1)) (aux (Tlam(var2, Int, texp2)) fn))
      | Tfix (var, tp, texp) ->
        fun x -> if fn x < fn "_" then fn x 
                  else if x = var then (aux texp (fun x -> if x = var then -1 else fn x)) "_"
                  else ((aux texp (fun x -> if x = var then -1 else fn x)) x)
      | Tifthenelse (texp, texp1, texp2) -> aux texp (aux texp1 (aux texp2 fn))
      | _ -> fn
    in
  let rec texp2exp' txp fn = 
    match txp with
      | Tvar var -> Ind (fn var)
      | Tlam (var, tp, texp) -> Lam (texp2exp' texp (fun x -> if x = var then 0 else (fn x)+1))
      | Tapp (texp1, texp2) -> App (texp2exp' texp1 (aux texp2 fn), texp2exp' texp2 fn)
      | Tpair (texp1, texp2) -> Pair (texp2exp' texp1 (aux texp2 fn), texp2exp' texp2 fn)
      | Tfst texp -> Fst (texp2exp' texp fn)
      | Tsnd texp -> Snd (texp2exp' texp fn)
      | Tinl (texp, tp) -> Inl (texp2exp' texp fn)
      | Tinr (texp, tp) -> Inr (texp2exp' texp fn)
      | Teunit -> Eunit
      | Tcase (texp, var1, texp1, var2, texp2) ->
        Case (texp2exp' texp (aux (Tlam(var1, Int, texp1)) (aux (Tlam(var2, Int, texp2)) fn)),
              texp2exp' texp1 (fun x -> if x = var1 then 0 else ((aux (Tlam (var2, Int, texp2)) fn) x)+1), 
              texp2exp' texp2 (fun x -> if x = var2 then 0 else (fn x)+1))
      | Tfix (var, tp, texp) -> Fix (texp2exp' texp (fun x -> if x = var then 0 else (fn x)+1))
      | Ttrue -> True
      | Tfalse -> False
      | Tifthenelse (texp, texp1, texp2) -> Ifthenelse (texp2exp' texp (aux texp1 (aux texp2 fn)), texp2exp' texp1 (aux texp2 fn), texp2exp' texp2 fn)
      | Tnum n -> Num n
      | Tplus -> Plus
      | Tminus -> Minus
      | Teq -> Eq
    in
  texp2exp' txp (fun x -> 0)
    
(* Problem 2. 
 * step1 : Tml.exp -> Tml.exp *)   

(*call by value*)

let rec is_value exp = 
  match exp with
  | Ind _ | Lam _ | Eunit | True | False | Num _
  | Plus | Minus | Eq                         -> true
  | Inl  e  | Inr  e                          -> is_value e
  | Pair (e1, e2)                             -> is_value e1 && is_value e2
  | Fst e | Snd e                             -> is_value e
  | App (e1, e2) ->
    begin match e1, e2 with
    | Lam _, _ -> false
    | Plus, Pair (Num n1, Num n2) -> false
    | Minus, Pair (Num n1, Num n2) -> false
    | Eq, Pair (Num n1, Num n2) -> false
    | _ -> is_value e1 && is_value e2
    end
  | Case (e, e1, e2) 
    -> if is_value e then false else false
  | Ifthenelse (e, e1, e2) 
    -> if is_value e then false else false
  | Fix _     -> false

let rec substitute exp' var num = 
  let rec shift term d bound = 
    match term with
    | Ind x -> if x < bound then Ind x else Ind (x + d)
    | Lam e -> Lam (shift e d (bound + 1))
    | App (e1, e2) -> App (shift e1 d bound, shift e2 d bound)
    | Pair (e1, e2) -> Pair (shift e1 d bound, shift e2 d bound)
    | Fst e -> Fst (shift e d bound)
    | Snd e -> Snd (shift e d bound)
    | Inl e -> Inl (shift e d bound)
    | Inr e -> Inr (shift e d bound)
    | Case (e, e1, e2) -> Case (shift e d bound, shift e1 d bound, shift e2 d bound)
    | Fix e -> Fix (shift e d (bound+1))
    | Ifthenelse (e, e1, e2) -> Ifthenelse (shift e d bound, shift e1 d bound, shift e2 d bound)
    | Eunit | True | False | Num _ | Plus | Minus | Eq as v -> v
  in
  match exp' with
  | Ind x -> 
    if x < num then Ind x 
    else if x = num then shift var num 0
    else Ind (x - 1)
  | Lam e -> Lam (substitute e var (num + 1))
  | App (e1, e2) -> App (substitute e1 var num, substitute e2 var num)
  | Pair (e1, e2) -> Pair (substitute e1 var num, substitute e2 var num)
  | Fst e -> Fst (substitute e var num)
  | Snd e -> Snd (substitute e var num)
  | Inl e -> Inl (substitute e var num)
  | Inr e -> Inr (substitute e var num)
  | Case (e, e1, e2) -> Case (substitute e var num, substitute e1 var num, substitute e2 var num)
  | Fix e -> Fix (substitute e var (num+1) )
  | Ifthenelse (e, e1, e2) -> Ifthenelse (substitute e var num, substitute e1 var num, substitute e2 var num)
  | Eunit | True | False | Num _ | Plus | Minus | Eq as v -> v

let rec step1 exp = 
  match exp with
  | Ind x -> raise Stuck
  | Lam e -> Lam (step1 e)
  | App (e1, e2) -> if is_value e1 then begin
    match e1, e2 with
    | Lam e, _ -> if is_value e2 then substitute e e2 0
                 else App (e1, step1 e2)
    | Plus, Pair (Num n1, Num n2) -> Num (n1 + n2)
    | Minus, Pair (Num n1, Num n2) -> Num (n1 - n2)
    | Eq, Pair (Num n1, Num n2) -> if n1 = n2 then True else False
    | (Plus | Minus | Eq), _ -> App (e1, step1 e2)
    | _ -> App (e1, step1 e2)
    end else App (step1 e1, e2)
  | Pair (e1, e2) -> 
    if is_value e1 then Pair (e1, step1 e2)
    else Pair (step1 e1, e2)
  | Fst e ->
    begin match e with 
      | Pair (e1, e2) when is_value e1 && is_value e2 -> e1
      | _ -> Fst (step1 e) 
    end
  | Snd e ->
    begin match e with 
      | Pair (e1, e2) when is_value e1 && is_value e2 -> e2
      | _ -> Snd (step1 e) 
    end
  | Inl e -> Inl (step1 e)
  | Inr e -> Inr (step1 e)
  | Case (e, e1, e2) -> 
    if is_value e then begin
      match e with
      | Inl v -> substitute e1 v 0
      | Inr v -> substitute e2 v 0
      | _ -> raise Stuck
    end else Case (step1 e, e1, e2)
  | Fix e ->
    let unfolded = substitute e (Fix e) 0 in
    unfolded
  | True | False -> raise Stuck
  | Ifthenelse (e, e1, e2) -> 
    begin match e with
      | True -> e1
      | False -> e2
      | _ -> Ifthenelse (step1 e, e1, e2)
    end
  | Eunit | Num _ | Plus | Minus | Eq -> raise Stuck


(* Problem 3. 
 * step2 : state -> state *)

(* fresh heap location generator *)
let fresh_loc =
  let counter = ref 0 in
  fun () -> let loc = !counter in counter := !counter + 1; loc

(* shift‑env : prepend a new location for de Bruijn 0 *)
let shift_env loc env = 
  fun n -> if n = 0 then loc else env (n - 1)

let rec eval_need heap exp env = 
  match exp with
  | Ind n -> 
    let loc = env n in
    let (heap', v) = force heap loc in
    (heap', v)
  | Lam e -> (heap, Lamv e)
  | App (e1, e2) ->
    let h1, v1 = eval_need heap e1 env in
    begin match v1 with
      | Lamv e -> 
        let (h2, loc) = Heap.allocate h1 (Delayed (e2, env)) in
        eval_need h2 e (shift_env loc env)
      | Plusv | Minusv | Eqv as prim ->
        let h2, v2 = eval_need h1 e2 env in
        begin match v2 with
          | Pairv (Num n1, Num n2) ->
            let result = 
              match prim with
              | Plusv -> Numv (n1 + n2)
              | Minusv -> Numv (n1 - n2)
              | Eqv -> if n1 = n2 then Truev else Falsev
              | _ -> raise Stuck
            in
            (h2, result)
          | _ -> raise Stuck
        end
      | _ ->
        let h2, v2 = eval_need h1 e2 env in
        (h2, Appv (value2exp v1, value2exp v2))
    end
  | Pair (e1, e2) ->
    let h1, v1 = eval_need heap e1 env in
    let h2, v2 = eval_need h1 e2 env in
    (h2, Pairv (value2exp v1, value2exp v2))
  | Fst e ->
    let h1, v1 = eval_need heap e env in
    begin match v1 with
      | Pairv (e1, e2) -> eval_need h1 e1 env
      | _ -> raise Stuck
    end
  | Snd e ->
    let h1, v1 = eval_need heap e env in
    begin match v1 with
      | Pairv (e1, e2) -> eval_need h1 e2 env
      | _ -> raise Stuck
    end
  | Eunit -> (heap, Eunitv)
  | Inl e -> let h1, v1 = eval_need heap e env in (h1, Inlv (value2exp v1))
  | Inr e -> let h1, v1 = eval_need heap e env in (h1, Inrv (value2exp v1))
  | Case (e, e1, e2) ->
    let h1, v1 = eval_need heap e env in
    begin match v1 with
      | Inlv v -> eval_need h1 (App (Lam e1, v)) env
      | Inrv v -> eval_need h1 (App (Lam e2, v)) env
      | _ -> raise Stuck
    end
  | Fix e -> eval_need heap (App (e, Fix e)) env
  | True -> (heap, Truev)
  | False -> (heap, Falsev)
  | Ifthenelse (e, e1, e2) ->
    let h1, v1 = eval_need heap e env in
    begin match v1 with
      | Truev -> eval_need h1 e1 env
      | Falsev -> eval_need h1 e2 env
      | _ -> raise Stuck
    end
  | Num n -> (heap, Numv n)
  | Plus -> (heap, Plusv)
  | Minus -> (heap, Minusv)
  | Eq -> (heap, Eqv)

(* force : make sure l contains a Computed value, returning (heap', value) *)
and force heap loc = 
  match Heap.deref heap loc with
  | Computed v -> (heap, v)
  | Delayed (e, env) ->
      let heap', v = eval_need heap e env in
      let heap'' = Heap.update heap' loc (Computed v) in
      (heap'', v)

(*call by name*)

let step2 st = 
  match st with
  | Anal_ST (heap, stack, exp, env) ->
    let heap', v = eval_need heap exp env in
    Return_ST (heap', stack, v)
  | Return_ST (heap, stack, v) ->
    raise Stuck

(* Problem 4. 
 * exp2string : Tml.exp -> string *)
                    
(* exp2string : Tml.exp -> string *)
let rec exp2string exp = 
  match exp with 
    Ind x -> string_of_int x
  | Lam e -> "(lam. " ^ (exp2string e) ^ ")"
  | App (e1, e2) -> "(" ^ (exp2string e1) ^ " " ^ (exp2string e2) ^ ")"
  | Pair (e1, e2) -> "(" ^ (exp2string e1) ^ "," ^ (exp2string e2) ^ ")"
  | Fst e -> "(fst " ^ (exp2string e) ^ ")"
  | Snd e -> "(snd " ^ (exp2string e) ^ ")"
  | Eunit -> "()"
  | Inl e -> "(inl " ^ (exp2string e) ^ ")"
  | Inr e -> "(inr " ^ (exp2string e) ^ ")"
  | Case (e, e1, e2) -> "(case " ^ (exp2string e) ^" of " ^ (exp2string e1) ^
                          " | " ^ (exp2string e2) ^ ")"
  | Fix e -> "(fix. "  ^ (exp2string e) ^ ")"
  | Ifthenelse (e, e1, e2) -> 
     "(if " ^ (exp2string e) ^ " then " ^ (exp2string e1) ^ 
       " else " ^ (exp2string e2) ^ ")"
  | True -> "true"  | False -> "false"
  | Num n -> "<" ^ (string_of_int n) ^ ">"
  | Plus -> "+"  | Minus -> "-" | Eq -> "="

(* state2string : state -> string 
 * you may modify this function for debugging your code *)
 let rec stack2string stack = 
  match stack with
  | Hole_SK -> "Hole_SK"
  | Frame_SK (inner_stack, frame) -> 
      (frame2string frame) ^ " |> " ^ (stack2string inner_stack)

and frame2string frame = 
  match frame with
  | Hole_F -> "Hole_F"
  | Value_F v -> "Value_F (" ^ exp2string (value2exp v) ^ ")"
  | Exp_F e -> "Exp_F (" ^ (exp2string e) ^ ")"
  | Lam_F f -> "Lam_F (" ^ (frame2string f) ^ ")"
  | App_F (f, e) -> "App_F (" ^ (frame2string f) ^ ", " ^ (exp2string e) ^ ")"
  | App_F' (e, f) -> "App_F' (" ^ (exp2string e) ^ ", " ^ (frame2string f) ^ ")"
  | Pair_F (f, e) -> "Pair_F (" ^ (frame2string f) ^ ", " ^ (exp2string e) ^ ")"
  | Pair_F' (e, f) -> "Pair_F' (" ^ (exp2string e) ^ ", " ^ (frame2string f) ^ ")"
  | Fst_F f -> "Fst_F (" ^ (frame2string f) ^ ")"
  | Snd_F f -> "Snd_F (" ^ (frame2string f) ^ ")"
  | Inl_F f -> "Inl_F (" ^ (frame2string f) ^ ")"
  | Inr_F f -> "Inr_F (" ^ (frame2string f) ^ ")"
  | Case_F (f, e1, e2) -> "Case_F (" ^ (frame2string f) ^ ", " ^ (exp2string e1) ^ ", " ^ (exp2string e2) ^ ")"
  | Ifthenelse_F (f, e1, e2) -> "Ifthenelse_F (" ^ (frame2string f) ^ ", " ^ (exp2string e1) ^ ", " ^ (exp2string e2) ^ ")"
  | Fix_F f -> "Fix_F (" ^ (frame2string f) ^ ")"

let state2string st = match st with
  | Anal_ST (heap, stack, exp, env) ->
      "Anal_ST: stack = [" ^ (stack2string stack) ^ "], exp = " ^ (exp2string exp)
  | Return_ST (heap, stack, v) ->
      "Return_ST: stack = [" ^ (stack2string stack) ^ "], value = " ^ exp2string (value2exp v)

(* ------------------------------------------------------------- *)     
let stepOpt1 e = try Some (step1 e) with Stuck -> None
let stepOpt2 st = try Some (step2 st) with Stuck -> None

let rec multiStep1 e = try multiStep1 (step1 e) with Stuck -> e
let rec multiStep2 st = try multiStep2 (step2 st) with Stuck -> st

let stepStream1 e =
  let rec steps e = 
    match (stepOpt1 e) with
      None -> Stream.from (fun _ -> None)
    | Some e' -> Stream.icons e' (steps e')
  in 
  Stream.icons e (steps e)

let stepStream2 st =
  let rec steps st = 
    match (stepOpt2 st) with
      None -> Stream.from (fun _ -> None)
    | Some st' -> Stream.icons st' (steps st')
  in 
  Stream.icons st (steps st)
