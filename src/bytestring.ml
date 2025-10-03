open Byte
open ByteCompare
open Classes0
open Datatypes
open ReflectEq

module String =
 struct
  type t =
  | EmptyString
  | String of byte * t

  (** val append : t -> t -> t **)

  let rec append x y =
    match x with
    | EmptyString -> y
    | String (x0, xs) -> String (x0, (append xs y))

  (** val eqb : t -> t -> bool **)

  let rec eqb a b =
    match a with
    | EmptyString ->
      (match b with
       | EmptyString -> true
       | String (_, _) -> false)
    | String (x, xs) ->
      (match b with
       | EmptyString -> false
       | String (y, ys) -> if ByteCompare.eqb x y then eqb xs ys else false)

  (** val compare : t -> t -> comparison **)

  let rec compare xs ys =
    match xs with
    | EmptyString -> (match ys with
                      | EmptyString -> Eq
                      | String (_, _) -> Lt)
    | String (x, xs0) ->
      (match ys with
       | EmptyString -> Gt
       | String (y, ys0) ->
         (match ByteCompare.compare x y with
          | Eq -> compare xs0 ys0
          | x0 -> x0))

  (** val concat : t -> t list -> t **)

  let rec concat sep = function
  | [] -> EmptyString
  | s0 :: xs ->
    (match xs with
     | [] -> s0
     | _ :: _ -> append s0 (append sep (concat sep xs)))
 end

module StringOT =
 struct
  type t = String.t

  (** val compare : String.t -> String.t -> comparison **)

  let compare =
    String.compare

  (** val reflect_eq_string : t coq_ReflectEq **)

  let reflect_eq_string =
    String.eqb

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec reflect_eq_string)
 end

module Tree =
 struct
  type t =
  | Coq_string of String.t
  | Coq_append of t * t

  (** val to_rev_list_aux : t -> String.t list -> String.t list **)

  let rec to_rev_list_aux t0 acc =
    match t0 with
    | Coq_string s -> s :: acc
    | Coq_append (s, s') -> to_rev_list_aux s' (to_rev_list_aux s acc)

  (** val to_string_acc : String.t -> String.t list -> String.t **)

  let rec to_string_acc acc = function
  | [] -> acc
  | s :: xs -> to_string_acc (String.append s acc) xs

  (** val to_string : t -> String.t **)

  let to_string t0 =
    let l = to_rev_list_aux t0 [] in to_string_acc String.EmptyString l

  (** val string_of_list_aux : ('a1 -> t) -> t -> 'a1 list -> t **)

  let rec string_of_list_aux f sep = function
  | [] -> Coq_string String.EmptyString
  | a :: l0 ->
    (match l0 with
     | [] -> f a
     | _ :: _ ->
       Coq_append ((f a), (Coq_append (sep, (string_of_list_aux f sep l0)))))

  (** val string_of_list : ('a1 -> t) -> 'a1 list -> t **)

  let string_of_list f l =
    Coq_append ((Coq_string (String.String (Coq_x5b, String.EmptyString))),
      (Coq_append
      ((string_of_list_aux f (Coq_string (String.String (Coq_x2c,
         String.EmptyString))) l), (Coq_string (String.String (Coq_x5d,
      String.EmptyString))))))

  (** val print_list : ('a1 -> t) -> t -> 'a1 list -> t **)

  let print_list =
    string_of_list_aux

  (** val parens : bool -> t -> t **)

  let parens top s =
    if top
    then s
    else Coq_append ((Coq_string (String.String (Coq_x28,
           String.EmptyString))), (Coq_append (s, (Coq_string (String.String
           (Coq_x29, String.EmptyString))))))
 end
