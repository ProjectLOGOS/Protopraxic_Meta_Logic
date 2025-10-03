open Monad_utils

type __ = Obj.t

type ('t, 'e) result =
| Ok of 't
| Err of 'e

val coq_Monad_result : (__, 'a1) result coq_Monad
