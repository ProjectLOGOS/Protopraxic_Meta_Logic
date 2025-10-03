open MCReflect

type __ = Obj.t

(** val option_get : 'a1 -> 'a1 option -> 'a1 **)

let option_get default = function
| Some x0 -> x0
| None -> default

(** val option_default : ('a1 -> 'a2) -> 'a1 option -> 'a2 -> 'a2 **)

let option_default f o b =
  match o with
  | Some x -> f x
  | None -> b

(** val reflect_option_default :
    ('a1 -> bool) -> ('a1 -> 'a2 reflectT) -> 'a1 option -> __ reflectT **)

let reflect_option_default _ hp = function
| Some a -> Obj.magic hp a
| None -> ReflectT (Obj.magic ())
