open Monad_utils

type __ = Obj.t

type ('t, 'e) result =
| Ok of 't
| Err of 'e

(** val coq_Monad_result : (__, 'a1) result coq_Monad **)

let coq_Monad_result =
  { ret = (fun _ t -> Ok t); bind = (fun _ _ mt f ->
    match mt with
    | Ok t -> f t
    | Err e -> Err e) }
