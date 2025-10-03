open Datatypes

val abs : Float64.t -> Float64.t

val eqb : Float64.t -> Float64.t -> bool

val ltb : Float64.t -> Float64.t -> bool

val div : Float64.t -> Float64.t -> Float64.t

val normfr_mantissa : Float64.t -> Uint63.t

val frshiftexp : Float64.t -> Float64.t * Uint63.t

val infinity : Float64.t

val one : Float64.t

val zero : Float64.t

val is_nan : Float64.t -> bool

val is_zero : Float64.t -> bool

val is_infinity : Float64.t -> bool

val get_sign : Float64.t -> bool
