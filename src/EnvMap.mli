open Kernames

module EnvMap :
 sig
  type 'a t = 'a KernameMap.t

  val empty : 'a1 t

  val lookup : kername -> 'a1 t -> 'a1 option

  val add : kername -> 'a1 -> 'a1 t -> 'a1 t

  val remove : kername -> 'a1 t -> 'a1 t

  val of_global_env : (kername * 'a1) list -> 'a1 t
 end
