open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val mapi_rec : (nat -> 'a1 -> 'a2) -> 'a1 list -> nat -> 'a2 list **)

let rec mapi_rec f l n =
  match l with
  | [] -> []
  | hd :: tl -> (f n hd) :: (mapi_rec f tl (S n))

(** val mapi : (nat -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let mapi f l =
  mapi_rec f l O

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f l l' =
  match l with
  | [] -> []
  | hd :: tl ->
    (match l' with
     | [] -> []
     | hd' :: tl' -> (f hd hd') :: (map2 f tl tl'))

(** val rev : 'a1 list -> 'a1 list **)

let rev l =
  let rec aux l0 acc =
    match l0 with
    | [] -> acc
    | x :: l1 -> aux l1 (x :: acc)
  in aux l []

(** val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rev_map f l =
  let rec aux l0 acc =
    match l0 with
    | [] -> acc
    | x :: l1 -> aux l1 ((f x) :: acc)
  in aux l []

(** val chop : nat -> 'a1 list -> 'a1 list * 'a1 list **)

let rec chop n l =
  match n with
  | O -> ([], l)
  | S n0 ->
    (match l with
     | [] -> ([], [])
     | hd :: tl -> let (l0, r) = chop n0 tl in ((hd :: l0), r))

(** val unfold : nat -> (nat -> 'a1) -> 'a1 list **)

let rec unfold n f =
  match n with
  | O -> []
  | S n0 -> app (unfold n0 f) ((f n0) :: [])

(** val map_In : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list **)

let rec map_In l f =
  match l with
  | [] -> []
  | y :: l0 -> (f y __) :: (map_In l0 (fun x _ -> f x __))

(** val map_InP : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list **)

let rec map_InP l f =
  match l with
  | [] -> []
  | a :: l0 -> (f a __) :: (map_InP l0 (fun x _ -> f x __))
