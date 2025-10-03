
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a reflectT =
| ReflectT of 'a
| ReflectF

(** val equiv_reflectT : bool -> (__ -> 'a1) -> 'a1 reflectT **)

let equiv_reflectT b x =
  if b then ReflectT (x __) else ReflectF

(** val elimT : bool -> 'a1 reflectT -> 'a1 **)

let elimT _ = function
| ReflectT t -> t
| ReflectF -> assert false (* absurd case *)
