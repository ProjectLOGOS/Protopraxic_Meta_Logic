open Ascii
open Bool
open Byte
open Datatypes
open List0

type string =
| EmptyString
| String of ascii * string

(** val string_rect :
    'a1 -> (ascii -> string -> 'a1 -> 'a1) -> string -> 'a1 **)

let rec string_rect f f0 = function
| EmptyString -> f
| String (a, s0) -> f0 a s0 (string_rect f f0 s0)

(** val string_rec :
    'a1 -> (ascii -> string -> 'a1 -> 'a1) -> string -> 'a1 **)

let rec string_rec f f0 = function
| EmptyString -> f
| String (a, s0) -> f0 a s0 (string_rec f f0 s0)

(** val string_dec : string -> string -> bool **)

let rec string_dec s x =
  match s with
  | EmptyString -> (match x with
                    | EmptyString -> true
                    | String (_, _) -> false)
  | String (a, s0) ->
    (match x with
     | EmptyString -> false
     | String (a0, s1) -> if ascii_dec a a0 then string_dec s0 s1 else false)

(** val eqb : string -> string -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> true
     | String (_, _) -> false)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> false
     | String (c2, s2') -> if Ascii.eqb c1 c2 then eqb s1' s2' else false)

(** val eqb_spec : string -> string -> reflect **)

let rec eqb_spec s s2 =
  match s with
  | EmptyString ->
    (match s2 with
     | EmptyString -> ReflectT
     | String (_, _) -> ReflectF)
  | String (a, s0) ->
    (match s2 with
     | EmptyString -> ReflectF
     | String (a0, s1) ->
       (match Ascii.eqb_spec a a0 with
        | ReflectT -> eqb_spec s0 s1
        | ReflectF -> ReflectF))

(** val compare : string -> string -> comparison **)

let rec compare s1 s2 =
  match s1 with
  | EmptyString -> (match s2 with
                    | EmptyString -> Eq
                    | String (_, _) -> Lt)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> Gt
     | String (c2, s2') ->
       (match Ascii.compare c1 c2 with
        | Eq -> compare s1' s2'
        | x -> x))

(** val ltb : string -> string -> bool **)

let ltb s1 s2 =
  match compare s1 s2 with
  | Lt -> true
  | _ -> false

(** val leb : string -> string -> bool **)

let leb s1 s2 =
  match compare s1 s2 with
  | Gt -> false
  | _ -> true

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

(** val length : string -> nat **)

let rec length = function
| EmptyString -> O
| String (_, s') -> S (length s')

(** val get : nat -> string -> ascii option **)

let rec get n = function
| EmptyString -> None
| String (c, s') -> (match n with
                     | O -> Some c
                     | S n' -> get n' s')

(** val substring : nat -> nat -> string -> string **)

let rec substring n m s =
  match n with
  | O ->
    (match m with
     | O -> EmptyString
     | S m' ->
       (match s with
        | EmptyString -> s
        | String (c, s') -> String (c, (substring O m' s'))))
  | S n' ->
    (match s with
     | EmptyString -> s
     | String (_, s') -> substring n' m s')

(** val concat : string -> string list -> string **)

let rec concat sep = function
| [] -> EmptyString
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> append x (append sep (concat sep xs)))

(** val prefix : string -> string -> bool **)

let rec prefix s1 s2 =
  match s1 with
  | EmptyString -> true
  | String (a, s1') ->
    (match s2 with
     | EmptyString -> false
     | String (b, s2') -> if ascii_dec a b then prefix s1' s2' else false)

(** val index : nat -> string -> string -> nat option **)

let rec index n s1 s2 = match s2 with
| EmptyString ->
  (match n with
   | O -> (match s1 with
           | EmptyString -> Some O
           | String (_, _) -> None)
   | S _ -> None)
| String (_, s2') ->
  (match n with
   | O ->
     if prefix s1 s2
     then Some O
     else (match index O s1 s2' with
           | Some n0 -> Some (S n0)
           | None -> None)
   | S n' ->
     (match index n' s1 s2' with
      | Some n0 -> Some (S n0)
      | None -> None))

(** val findex : nat -> string -> string -> nat **)

let findex n s1 s2 =
  match index n s1 s2 with
  | Some n0 -> n0
  | None -> O

(** val string_of_list_ascii : ascii list -> string **)

let rec string_of_list_ascii = function
| [] -> EmptyString
| ch :: s0 -> String (ch, (string_of_list_ascii s0))

(** val list_ascii_of_string : string -> ascii list **)

let rec list_ascii_of_string = function
| EmptyString -> []
| String (ch, s0) -> ch :: (list_ascii_of_string s0)

(** val string_of_list_byte : byte list -> string **)

let string_of_list_byte s =
  string_of_list_ascii (map ascii_of_byte s)

(** val list_byte_of_string : string -> byte list **)

let list_byte_of_string s =
  map byte_of_ascii (list_ascii_of_string s)

module StringSyntax =
 struct
 end

(** val coq_HelloWorld : string **)

let coq_HelloWorld =
  String ((Ascii (true, false, false, true, false, false, false, false)),
    (String ((Ascii (false, true, false, false, false, true, false, false)),
    (String ((Ascii (false, false, false, true, false, false, true, false)),
    (String ((Ascii (true, false, true, false, false, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (true, true, true, true, false, true, true, false)),
    (String ((Ascii (false, false, false, false, false, true, false, false)),
    (String ((Ascii (true, true, true, false, true, true, true, false)),
    (String ((Ascii (true, true, true, true, false, true, true, false)),
    (String ((Ascii (false, true, false, false, true, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (false, false, true, false, false, true, true, false)),
    (String ((Ascii (true, false, false, false, false, true, false, false)),
    (String ((Ascii (false, true, false, false, false, true, false, false)),
    (String ((Ascii (true, true, true, false, false, false, false, false)),
    (String ((Ascii (false, true, false, true, false, false, false, false)),
    EmptyString)))))))))))))))))))))))))))))))))
