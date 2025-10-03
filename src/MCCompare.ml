open Classes0
open Datatypes
open Orders

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module ListOrderedType =
 functor (A:UsualOrderedType) ->
 struct
  type t = A.t list

  (** val compare : t -> t -> comparison **)

  let rec compare l1 l2 =
    match l1 with
    | [] -> (match l2 with
             | [] -> Eq
             | _ :: _ -> Lt)
    | hd :: tl ->
      (match l2 with
       | [] -> Gt
       | hd' :: tl' ->
         (match A.compare hd hd' with
          | Eq -> compare tl tl'
          | x -> x))

  (** val lt__sig_pack : t -> t -> (t * t) * __ **)

  let lt__sig_pack x x0 =
    (x,x0),__

  (** val lt__Signature : t -> t -> (t * t) * __ **)

  let lt__Signature =
    lt__sig_pack

  (** val eqb : t -> t -> bool **)

  let eqb l1 l2 =
    match compare l1 l2 with
    | Eq -> true
    | _ -> false

  (** val eqb_dec : t -> t -> bool **)

  let eqb_dec x y =
    let filtered_var = eqb x y in if filtered_var then true else false

  (** val eq_dec : t coq_EqDec **)

  let eq_dec =
    eqb_dec
 end
