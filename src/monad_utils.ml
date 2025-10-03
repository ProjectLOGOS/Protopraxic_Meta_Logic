
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_Monad = { ret : (__ -> __ -> 'm);
                      bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 coq_Monad -> 'a2 -> 'a1 **)

let ret monad x =
  Obj.magic monad.ret __ x

(** val bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let bind monad x x0 =
  Obj.magic monad.bind __ __ x x0

type ('e, 'm) coq_MonadExc = { raise : (__ -> 'e -> 'm);
                               catch : (__ -> 'm -> ('e -> 'm) -> 'm) }

(** val raise : ('a1, 'a2) coq_MonadExc -> 'a1 -> 'a2 **)

let raise monadExc x =
  monadExc.raise __ x

(** val option_monad : __ option coq_Monad **)

let option_monad =
  { ret = (fun _ a -> Some a); bind = (fun _ _ m f ->
    match m with
    | Some a -> f a
    | None -> None) }

(** val mapopt : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec mapopt f = function
| [] -> ret (Obj.magic option_monad) []
| x :: xs ->
  bind (Obj.magic option_monad) (Obj.magic f x) (fun x' ->
    bind (Obj.magic option_monad) (mapopt f xs) (fun xs' ->
      ret (Obj.magic option_monad) (x' :: xs')))
