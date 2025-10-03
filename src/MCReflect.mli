
type __ = Obj.t

type 'a reflectT =
| ReflectT of 'a
| ReflectF

val equiv_reflectT : bool -> (__ -> 'a1) -> 'a1 reflectT

val elimT : bool -> 'a1 reflectT -> 'a1
