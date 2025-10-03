open BasicAst
open Datatypes
open EAst
open EAstUtils
open EPrimitive
open Kernames

type __ = Obj.t

module MkAppsInd :
 sig
  val inspect : 'a1 -> 'a1

  val case_clause_7 :
    (term -> term list -> __ -> __ -> 'a1) -> term -> term -> (term * term
    list) -> 'a1

  val case :
    'a1 -> (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> 'a1) ->
    (name -> term -> 'a1) -> (name -> term -> term -> 'a1) -> (term -> term
    list -> __ -> __ -> 'a1) -> (kername -> 'a1) -> (inductive -> nat -> term
    list -> 'a1) -> ((inductive * nat) -> term -> (name list * term) list ->
    'a1) -> (projection -> term -> 'a1) -> (term mfixpoint -> nat -> 'a1) ->
    (term mfixpoint -> nat -> 'a1) -> (term prim_val -> 'a1) -> (term -> 'a1)
    -> (term -> 'a1) -> term -> 'a1
 end
