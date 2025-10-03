open Kernames

module EnvMap =
 struct
  type 'a t = 'a KernameMap.t

  (** val empty : 'a1 t **)

  let empty =
    KernameMap.empty

  (** val lookup : kername -> 'a1 t -> 'a1 option **)

  let lookup =
    KernameMap.find

  (** val add : kername -> 'a1 -> 'a1 t -> 'a1 t **)

  let add =
    KernameMap.add

  (** val remove : kername -> 'a1 t -> 'a1 t **)

  let remove =
    KernameMap.remove

  (** val of_global_env : (kername * 'a1) list -> 'a1 t **)

  let of_global_env =
    KernameMapFact.of_list
 end
