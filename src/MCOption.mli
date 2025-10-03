open MCReflect

type __ = Obj.t

val option_get : 'a1 -> 'a1 option -> 'a1

val option_default : ('a1 -> 'a2) -> 'a1 option -> 'a2 -> 'a2

val reflect_option_default :
  ('a1 -> bool) -> ('a1 -> 'a2 reflectT) -> 'a1 option -> __ reflectT
