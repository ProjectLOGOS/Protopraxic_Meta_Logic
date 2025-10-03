open Datatypes
open Decimal

module Nat :
 sig
  val pred : nat -> nat

  val add : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint

  val eq_dec : nat -> nat -> bool
 end
