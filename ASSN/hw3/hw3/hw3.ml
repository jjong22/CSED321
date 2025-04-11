open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1

  let (++) x y = x + y
  let ( ** ) x y = x * y
  let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true

  let (++) x y = x || y
  
  let ( ** ) x y = x && y

  let (==) x y = x = y
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list

  exception VectorIllegal

  let create l = 
    if l = [] then raise VectorIllegal
    else l

  let to_list v = v

  let rec dim v =
    match v with
    | [] -> 0
    | [x] -> 1
    | hd :: tl -> 1 + dim tl

  let rec nth (v:t) (n:int) : elem = 
    match v with
    | [] -> raise VectorIllegal
    | hd::tl ->
      if n == 0 then hd
      else nth tl (n-1)

  let rec (++) (x:t) (y:t) =
    match (x, y) with
    | ([], []) -> []
    | ([], y_l) -> raise VectorIllegal
    | (x_l, []) -> raise VectorIllegal
    | (hd_x::tl_x, hd_y::tl_y) -> (Scal.(++) hd_x hd_y) :: ((++) tl_x tl_y)

  let rec (==) (x:t) (y:t) = 
  match (x, y) with
  | ([], []) -> true
  | ([], y_l) -> raise VectorIllegal
  | (x_l, []) -> raise VectorIllegal
  | (hd_x::tl_x, hd_y::tl_y) -> (Scal.(==) hd_x hd_y) && ((==) tl_x tl_y)

  let rec innerp (x:t) (y:t) =
    match (x, y) with
  | ([], []) -> Scal.zero
  | ([], y_l) -> raise VectorIllegal
  | (x_l, []) -> raise VectorIllegal
  | (hd_x::tl_x, hd_y::tl_y) -> (Scal.(++) (Scal.( ** ) hd_x hd_y) (innerp tl_x tl_y))

end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list list

  exception MatrixIllegal

  let create ll = 
    match ll with
    | [] -> raise MatrixIllegal
    | [x] -> ll
    | x::y::tl -> 
      if List.length x = List.length y then ll
      else raise MatrixIllegal

  let identity n : t = 
    let mat = ref [] in
    for i = 1 to n do
      let sublist = ref [] in
      for j = 1 to n do
        if i = j then sublist := !sublist @ [Scal.one]
        else sublist := !sublist @ [Scal.zero]
      done;
      mat := !mat @ [!sublist]
    done;
    !mat


  let rec dim m =
    match m with
    | [] -> 0
    | hd::tl -> 1 + (dim tl)

  let rec transpose m = 
    match m with
    | [] -> []
    | [] :: xss -> transpose xss
    | (x::xs)::xss -> (x::List.map List.hd xss) :: transpose (xs::List.map List.tl xss)

  let to_list m = m

  let get m r c = 
    try
      let row = List.nth m r in
      List.nth row c
    with Failure _ -> raise MatrixIllegal

  let (++) m1 m2 =
    if dim m1 <> dim m2 then raise MatrixIllegal
    else
      let rec add_row r1 r2 =
        match (r1, r2) with
        | ([], []) -> []
        | (x::xs, y::ys) -> (Scal.(++) x y) :: add_row xs ys
        | _ -> raise MatrixIllegal
      in
      List.map2 add_row m1 m2
    
  let ( ** ) m1 m2 : t =
    let trans_mat = transpose m2 in
    let dot_product v1 v2 =
      List.fold_left2 (fun acc x y -> Scal.(++) acc (Scal.( ** ) x y)) Scal.zero v1 v2
    in
    List.map (fun row -> List.map (dot_product row) trans_mat) m1

  let (==) m1 m2 = 
    if dim m1 <> dim m2 then raise MatrixIllegal
    else 
      let rec comp_row r1 r2 =
        match (r1, r2) with
        | ([], []) -> true
        | (x::xs, y::ys) -> (Scal.(==) x y) && (comp_row xs ys)
        | _ -> raise MatrixIllegal
      in
      List.for_all (fun x -> x) (List.map2 comp_row m1 m2)

end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure m =
    let id = Mat.identity (Mat.dim m) in
    let rec aux current_closure =
      let next_closure = Mat.(++) id (Mat.( ** ) current_closure m) in
      if Mat.(==) current_closure next_closure
        then current_closure
      else aux next_closure
  in 
  aux id
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach ll =
  BoolMat.to_list (BoolMatClosure.closure (BoolMat.create ll))

let al = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  false; false];
   [false; true;  true;  false; true;  false];
   [false; true;  false; true;  true;  true];
   [false; false; true;  true;  true;  false];
   [false; false; false; true;  false; true]]

let solution_al' = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = -1
  let one = 0

  let (++) x y =
    if x = zero then y
    else if y = zero then x
    else min x y
  
  let ( ** ) x y =
    if x = zero || y = zero then zero
    else x + y

  let (==) x y = 
    x = y 
end

module DistanceMat = MatrixFn (Distance)
module DistanceMatClosure = ClosureFn (DistanceMat)

let distance ll = 
  DistanceMat.to_list (DistanceMatClosure.closure (DistanceMat.create ll))

let dl =
  [[  0;  -1;  -1;  -1;  -1;  -1 ];
   [ -1; 0  ; 35 ; 200; -1 ; -1  ];
   [ -1; 50 ; 0  ; -1 ; 150; -1  ];
   [ -1; 75;  -1 ; 0  ; 100; 25  ];
   [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
   [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
  [[0;  -1;  -1;  -1;  -1;  -1  ];
   [-1; 0;   35;  200; 185; 225 ];
   [-1; 50;  0;   215; 150; 240 ];
   [-1; 75;  110; 0;   100; 25  ];
   [-1; 100; 50;  65;  0;   90  ];
   [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = -1

  let (++) x y =
    if x = one || y = one then one
    else max x y
  
  let ( ** ) x y =
    if x = one then y
    else if y = one then x
    else min x y

  let (==) x y = 
    x = y 
end

module WeightMat = MatrixFn (Weight)
module WeightMatClosure = ClosureFn (WeightMat)

let weight ll = 
  WeightMat.to_list (WeightMatClosure.closure (WeightMat.create ll))

let ml =
  [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
   [0 ; -1 ; 10 ; 100; 0  ; 0   ];
   [0 ; 50 ; -1 ; 0  ; 150; 0   ];
   [0 ; 75 ; 0  ; -1 ; 125; 40 ];
   [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
   [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
  [[-1; 0;  0;   0;   0;   0  ];
   [0;  -1; 25;  100; 100; 40 ];
   [0;  75; -1;  150; 150; 40 ];
   [0;  75; 25;  -1;  125; 40 ];
   [0;  75; 25;  -1;  -1;  40 ];
   [0;  0;  0;   0;   0;   -1 ]]

let _ =
  try 
  if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
    print_endline "\nYour program seems fine (but no guarantee)!"
  else
    print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!" 

