exception Not_implemented

type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree

let rec sum n = 
  if n = 0 then 0
  else sum (n-1) + n

let rec power x n = 
  if n = 0 then 1
  else (power (x)(n-1)) * x

let rec gcd m n =
  if (n < m) then gcd (n)(m) (*change*)
  else if (n mod m = 0) then m
  else gcd (n mod m) (m)

let rec combi n k =
  if k = 0 then 1
  else (combi (n-1) (k-1)) * n / k

let rec sum_tree t =
  match t with
  | Leaf v -> v
  | Node (left_node, v, right_node) -> v + sum_tree left_node + sum_tree right_node

let rec depth t =
  match t with
  | Leaf v -> 1
  | Node (left_node, v, right_node) -> 1 + if (depth left_node < depth right_node) then depth left_node else depth right_node

let rec bin_search t x =
  match t with
  | Leaf v -> v = x
  | Node (left_node, v, right_node) -> if x=v then true else if x<v then bin_search left_node x else bin_search right_node x

let rec postorder t = 
  match t with
  | Leaf v -> [v]
  | Node (left_node, v, right_node) -> postorder left_node @ postorder right_node @ [v]

let rec max l = 
  match l with
  | [] -> 0
  | _ :: num -> if List.nth l 0 > max (List.tl l) then List.nth l 0 else max (List.tl l)

let rec list_add l1 l2 =
  if List.length l1 = 0 then
    if List.length l2 = 0 then []
    else l2
  else if List.length l2 = 0 then l1
  else [List.nth l1 0 + List.nth l2 0] @ list_add (List.tl l1) (List.tl l2)

let rec insert m l =
  if List.length l = 0 then [m] 
  else if m < List.nth l 0 then [m] @ l
  else [List.nth l 0] @ insert (m) (List.tl l)

let rec insort l =
  if List.length l = 0 then []
  else insert (List.nth l 0) (insort(List.tl l))

let rec compose f g =
  fun x -> g (f x)

let rec curry f x y =
  f(x, y)

let rec uncurry f (x,y) =
  f x y

let rec multifun f n =
  if n = 1 then f
  else compose (f) ( multifun f (n-1) )

let rec ltake l n =
  if List.length l < n then l
  else if n = 0 then []
  else [List.nth l 0] @ ltake (List.tl l) (n-1)

let rec lall f l =
  if List.length l = 0 then true
  else (f (List.nth l 0)) && lall (f) (List.tl l)

let rec lmap f l = 
  if List.length l = 0 then []
  else [f (List.nth l 0)] @ lmap (f) (List.tl l)

let rec lrev l = 
  if List.length l = 0 then []
  else lrev (List.tl l) @ [List.nth l 0]

let rec lflat l =
  if List.length l = 0 then []
  else (List.nth l 0) @ lflat (List.tl l)

let rec lzip l1 l2 =
  if List.length l1 = 0 then []
  else if List.length l2 = 0 then []
  else [ (List.nth l1 0, List.nth l2 0) ] @ lzip (List.tl l1) (List.tl l2)

let rec split l =
  match l with
  | [] -> ([], [])
  | [x] -> ([x], [])
  | x::y::xs -> let (left, right) = split xs in (x::left, y::right)  
    
let rec cartprod l1 l2 =
  match l1 with
  | [] -> []
  | element :: sub_l1 -> (lmap (fun x -> (element, x)) l2) @ (cartprod sub_l1 l2)

let rec powerset l = 
  match l with
  | [] -> [[]]
  | element :: sublist -> 
    let tail_powerset = powerset sublist in 
    tail_powerset @ (lmap (fun x -> element :: x) tail_powerset)
