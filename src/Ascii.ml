open BinNat
open BinNums
open Bool
open Byte
open Datatypes

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val ascii_dec : ascii -> ascii -> bool **)

let ascii_dec a b =
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  if bool_dec b0 b8
  then if bool_dec b1 b9
       then if bool_dec b2 b10
            then if bool_dec b3 b11
                 then if bool_dec b4 b12
                      then if bool_dec b5 b13
                           then if bool_dec b6 b14
                                then bool_dec b7 b15
                                else false
                           else false
                      else false
                 else false
            else false
       else false
  else false

(** val eqb : ascii -> ascii -> bool **)

let eqb a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  if if if if if if if eqb a0 b0 then eqb a1 b1 else false
                 then eqb a2 b2
                 else false
              then eqb a3 b3
              else false
           then eqb a4 b4
           else false
        then eqb a5 b5
        else false
     then eqb a6 b6
     else false
  then eqb a7 b7
  else false

(** val eqb_spec : ascii -> ascii -> reflect **)

let eqb_spec a b =
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match eqb_spec b0 b8 with
   | ReflectT ->
     (match eqb_spec b1 b9 with
      | ReflectT ->
        (match eqb_spec b2 b10 with
         | ReflectT ->
           (match eqb_spec b3 b11 with
            | ReflectT ->
              (match eqb_spec b4 b12 with
               | ReflectT ->
                 (match eqb_spec b5 b13 with
                  | ReflectT ->
                    (match eqb_spec b6 b14 with
                     | ReflectT -> eqb_spec b7 b15
                     | ReflectF -> ReflectF)
                  | ReflectF -> ReflectF)
               | ReflectF -> ReflectF)
            | ReflectF -> ReflectF)
         | ReflectF -> ReflectF)
      | ReflectF -> ReflectF)
   | ReflectF -> ReflectF)

(** val coq_N_of_digits : bool list -> coq_N **)

let rec coq_N_of_digits = function
| [] -> N0
| b :: l' ->
  N.add (if b then Npos Coq_xH else N0)
    (N.mul (Npos (Coq_xO Coq_xH)) (coq_N_of_digits l'))

(** val coq_N_of_ascii : ascii -> coq_N **)

let coq_N_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  coq_N_of_digits
    (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: []))))))))

(** val compare : ascii -> ascii -> comparison **)

let compare a b =
  N.compare (coq_N_of_ascii a) (coq_N_of_ascii b)

(** val ascii_of_byte : byte -> ascii **)

let ascii_of_byte b =
  let (b0, p) = to_bits b in
  let (b1, p0) = p in
  let (b2, p1) = p0 in
  let (b3, p2) = p1 in
  let (b4, p3) = p2 in
  let (b5, p4) = p3 in
  let (b6, b7) = p4 in Ascii (b0, b1, b2, b3, b4, b5, b6, b7)

(** val byte_of_ascii : ascii -> byte **)

let byte_of_ascii = function
| Ascii (b0, b1, b2, b3, b4, b5, b6, b7) ->
  of_bits (b0, (b1, (b2, (b3, (b4, (b5, (b6, b7)))))))
