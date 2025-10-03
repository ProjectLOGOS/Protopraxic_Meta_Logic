open Datatypes

(** val abs : Float64.t -> Float64.t **)

let abs = Float64.abs

(** val eqb : Float64.t -> Float64.t -> bool **)

let eqb = Float64.eq

(** val ltb : Float64.t -> Float64.t -> bool **)

let ltb = Float64.lt

(** val div : Float64.t -> Float64.t -> Float64.t **)

let div = Float64.div

(** val normfr_mantissa : Float64.t -> Uint63.t **)

let normfr_mantissa = Float64.normfr_mantissa

(** val frshiftexp : Float64.t -> Float64.t * Uint63.t **)

let frshiftexp = Float64.frshiftexp

(** val infinity : Float64.t **)

let infinity =
  (Float64.of_float (infinity))

(** val one : Float64.t **)

let one =
  (Float64.of_float (0x1p+0))

(** val zero : Float64.t **)

let zero =
  (Float64.of_float (0x0p+0))

(** val is_nan : Float64.t -> bool **)

let is_nan f =
  negb (eqb f f)

(** val is_zero : Float64.t -> bool **)

let is_zero f =
  eqb f zero

(** val is_infinity : Float64.t -> bool **)

let is_infinity f =
  eqb (abs f) infinity

(** val get_sign : Float64.t -> bool **)

let get_sign f =
  let f0 = if is_zero f then div one f else f in ltb f0 zero
