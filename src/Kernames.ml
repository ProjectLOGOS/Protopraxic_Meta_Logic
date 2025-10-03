open Byte
open Classes0
open Datatypes
open FMapAVL
open FMapFacts
open Int0
open List0
open MCCompare
open MCString
open MSetAVL
open OrderedType0
open PeanoNat
open ReflectEq
open Bytestring

type __ = Obj.t

type ident = String.t

type dirpath = ident list

module IdentOT = StringOT

module DirPathOT = ListOrderedType(IdentOT)

(** val string_of_dirpath : dirpath -> String.t **)

let string_of_dirpath dp =
  String.concat (String.String (Coq_x2e, String.EmptyString)) (rev dp)

type modpath =
| MPfile of dirpath
| MPbound of dirpath * ident * nat
| MPdot of modpath * ident

(** val string_of_modpath : modpath -> String.t **)

let rec string_of_modpath = function
| MPfile dp -> string_of_dirpath dp
| MPbound (dp, id, n) ->
  String.append (string_of_dirpath dp)
    (String.append (String.String (Coq_x2e, String.EmptyString))
      (String.append id
        (String.append (String.String (Coq_x2e, String.EmptyString))
          (string_of_nat n))))
| MPdot (mp0, id) ->
  String.append (string_of_modpath mp0)
    (String.append (String.String (Coq_x2e, String.EmptyString)) id)

type kername = modpath * ident

(** val string_of_kername : kername -> String.t **)

let string_of_kername kn =
  String.append (string_of_modpath (fst kn))
    (String.append (String.String (Coq_x2e, String.EmptyString)) (snd kn))

module ModPathComp =
 struct
  (** val mpbound_compare :
      DirPathOT.t -> String.t -> nat -> DirPathOT.t -> String.t -> nat ->
      comparison **)

  let mpbound_compare dp id k dp' id' k' =
    match DirPathOT.compare dp dp' with
    | Eq ->
      (match IdentOT.compare id id' with
       | Eq -> Nat.compare k k'
       | x -> x)
    | x -> x

  (** val compare : modpath -> modpath -> comparison **)

  let rec compare mp mp' =
    match mp with
    | MPfile dp ->
      (match mp' with
       | MPfile dp' -> DirPathOT.compare dp dp'
       | _ -> Gt)
    | MPbound (dp, id, k) ->
      (match mp' with
       | MPfile _ -> Lt
       | MPbound (dp', id', k') -> mpbound_compare dp id k dp' id' k'
       | MPdot (_, _) -> Gt)
    | MPdot (mp0, id) ->
      (match mp' with
       | MPdot (mp'0, id') ->
         (match compare mp0 mp'0 with
          | Eq -> IdentOT.compare id id'
          | x -> x)
       | _ -> Lt)
 end

module KernameComp =
 struct
  type t = kername

  (** val compare :
      (modpath * String.t) -> (modpath * String.t) -> comparison **)

  let compare kn kn' =
    let (mp, id) = kn in
    let (mp', id') = kn' in
    (match ModPathComp.compare mp mp' with
     | Eq -> IdentOT.compare id id'
     | x -> x)
 end

module Kername =
 struct
  type t = kername

  (** val compare :
      (modpath * String.t) -> (modpath * String.t) -> comparison **)

  let compare kn kn' =
    let (mp, id) = kn in
    let (mp', id') = kn' in
    (match ModPathComp.compare mp mp' with
     | Eq -> IdentOT.compare id id'
     | x -> x)

  module OT = OrderedTypeAlt.OrderedType_from_Alt(KernameComp)

  (** val eqb : (modpath * String.t) -> (modpath * String.t) -> bool **)

  let eqb kn kn' =
    match compare kn kn' with
    | Eq -> true
    | _ -> false

  (** val reflect_kername : kername coq_ReflectEq **)

  let reflect_kername =
    eqb

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec reflect_kername)
 end

module KernameMap = FMapAVL.Make(Kername.OT)

module KernameMapFact = WProperties(KernameMap)

module KernameSet = Make(Kername)

type inductive = { inductive_mind : kername; inductive_ind : nat }

(** val string_of_inductive : inductive -> String.t **)

let string_of_inductive i =
  String.append (string_of_kername i.inductive_mind)
    (String.append (String.String (Coq_x2c, String.EmptyString))
      (string_of_nat i.inductive_ind))

(** val eq_inductive_def : inductive -> inductive -> bool **)

let eq_inductive_def i i' =
  let { inductive_mind = i0; inductive_ind = n } = i in
  let { inductive_mind = i'0; inductive_ind = n' } = i' in
  reflect_prod Kername.reflect_kername reflect_nat (i0, n) (i'0, n')

(** val reflect_eq_inductive : inductive coq_ReflectEq **)

let reflect_eq_inductive =
  eq_inductive_def

type projection = { proj_ind : inductive; proj_npars : nat; proj_arg : nat }
