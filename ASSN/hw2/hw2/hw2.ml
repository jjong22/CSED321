exception NotImplemented
	    
type 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
						      
(** Recursive functions **)

let rec lrev l =
  if List.length l = 0 then []
  else lrev (List.tl l) @ [List.nth l 0]

let rec lrevrev l =
  match l with
  | [] -> []
  | hd::tl -> lrevrev tl @ [lrev hd]

let rec lfoldl f e l =
  match l with
  | [] -> e
  | [x] -> f (x, e)
  | hd::tl -> lfoldl f (f (hd, e)) tl

(** Tail recursive functions  **)

let fact n =
  let rec sub_func tmp x =
    match x with
    | 0 -> tmp
    | x -> sub_func (tmp * x) (x-1)
  in 
  sub_func 1 n

let fib n =
  let rec sub_func x a b = 
    match x with
    | 0 -> a
    | 1 -> b
    | x -> sub_func (x-1) (b) (a+b)
  in
  sub_func n 1 1
    
let alterSum l = 
  let rec sub_func sublist sum flag = 
    match sublist with
    | [] -> (sum + 0)
    | hd::tl -> 
      if flag then sub_func tl (sum + hd) (false)
      else sub_func tl (sum - hd) (true)
  in
  sub_func l 0 true

let ltabulate n f =
  let rec sub_func result_list cnt =
    match cnt with
    | 0 -> [f 0] @ result_list
    | x -> sub_func ([f x] @ result_list) (cnt-1)
  in
  sub_func [] n

let lfilter p l =
  let rec sub_func sublist result_list =
    match sublist with
    | [] -> result_list
    | hd::tl -> 
      if (p hd) then sub_func tl (result_list @ [hd])
      else sub_func tl result_list
  in
  sub_func l []

let union s t = 
  let rec sub_func unionlist sublist =
    match sublist with
    | [] -> unionlist
    | hd::tl -> 
      if List.mem hd unionlist then sub_func unionlist tl
      else sub_func (unionlist @ [hd]) tl
  in
  sub_func s t
      

let inorder t =
  let rec search subtree record =
    match subtree with
    | Leaf v -> v :: record
    | Node (left_node, value, right_node) ->
        let acc_with_right = search right_node record in   
        let acc_with_value = value :: acc_with_right in  
        search left_node acc_with_value                
  in
  search t []

	   
let postorder t =
  let rec search subtree record =
    match subtree with
    | Leaf v -> v :: record
    | Node (left_node, value, right_node) ->
        let acc_with_value = value :: record in  
        let acc_with_right = search right_node acc_with_value in   
        search left_node acc_with_right            
  in
  search t []

let preorder t =
  let rec search subtree record =
    match subtree with
    | Leaf v -> v :: record
    | Node (left_node, value, right_node) ->
        let acc_with_right = search right_node record in  
        let acc_with_left = search left_node acc_with_right in   
        value :: acc_with_left
  in
  search t []
		       
(** Sorting in the ascending order **)

let rec quicksort l =
  match l with
  | [] -> []
  | hd :: tl ->
    let rec partition lst left right =
      match lst with
      | [] -> (left, right)
      | x::xs -> 
        if x <= hd then
          partition xs (x::left) right
        else 
          partition xs left (x::right)
    in
    let left_list, right_list = partition tl [] [] in
    quicksort left_list @ [hd] @ quicksort right_list


let rec merge left right =
  match (left, right) with
  | ([], r) -> r
  | (l, []) -> l
  | (left_hd::left_tl, right_hd::right_tl) ->
    if left_hd <= right_hd then
      left_hd :: merge left_tl right
    else 
      right_hd :: merge left right_tl

let rec split l =
  match l with
  | [] -> ([], [])
  | [x] -> ([x], [])
  | x::y::xs -> let (left, right) = split xs in (x::left, y::right)

let rec mergesort l =
  match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
    let left, right = split l in
    merge (mergesort left) (mergesort right)
  
			
(** Structures **)

module type HEAP = 
  sig
    exception InvalidLocation
    type loc
    type 'a heap
    val empty : unit -> 'a heap
    val allocate : 'a heap -> 'a -> 'a heap * loc
    val dereference : 'a heap -> loc -> 'a 
    val update : 'a heap -> loc -> 'a -> 'a heap
  end
    
module type DICT =
  sig
    type key
    type 'a dict
    val empty : unit -> 'a dict
    val lookup : 'a dict -> key -> 'a option
    val delete : 'a dict -> key -> 'a dict
    val insert : 'a dict -> key * 'a -> 'a dict 
  end

module Heap : HEAP =
  struct
    exception InvalidLocation 
		
    type loc = int
    type 'a heap = (loc * 'a) list

    let empty() = []

    let allocate h v =  
      let l = List.length h in 
      (h @ [(l, v)], l)
    
    let rec dereference h l = 
      match h with
      | [] -> raise InvalidLocation
      | (loc, value)::tl -> 
        if l = loc then value
        else dereference tl l

    let rec update h l v =
      match h with
      | [] -> raise InvalidLocation
      | (loc, value)::tl -> 
        if l = loc then (l, v) :: tl
        else (loc, value) :: update tl l v
  end
    
module DictList : DICT with type key = string =
  struct
    type key = string
    type 'a dict = (key * 'a) list
			      
    let empty() = []

    let rec lookup d k =
      match d with
      | [] -> None
      | (key, value)::tl -> 
        if key = k then Some value
        else lookup tl k

    let rec delete d k =
      match d with
      | [] -> []
      | (key, value)::tl -> 
        if key = k then delete tl k
        else (key, value) :: delete tl k

    let rec insert d (k, v) =
      match d with
      | [] -> [(k, v)]
      | (key, value)::tl ->
        if key = k then (k, v) :: tl
        else (key, value) :: insert tl (k, v)
  end
    
module DictFun : DICT with type key = string =
  struct
    type key = string
    type 'a dict = key -> 'a option
			     
    let empty () = fun _ -> None
    let lookup d k = d k
    let delete d k = 
      fun x -> if x = k then None else d x
    let insert d (k, v) =
      fun x -> if x = k then Some v else d x
  end