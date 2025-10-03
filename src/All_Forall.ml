open CRelationClasses
open Datatypes
open List0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('a, 'p) coq_All =
| All_nil
| All_cons of 'a * 'a list * 'p * ('a, 'p) coq_All

type ('a, 'p) coq_Alli =
| Alli_nil
| Alli_cons of 'a * 'a list * 'p * ('a, 'p) coq_Alli

type ('a, 'b, 'r) coq_All2 =
| All2_nil
| All2_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2

(** val alli : (nat -> 'a1 -> bool) -> nat -> 'a1 list -> bool **)

let rec alli p n = function
| [] -> true
| hd :: tl -> (&&) (p n hd) (alli p (S n) tl)

(** val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec forallb2 f l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | hd :: tl ->
    (match l' with
     | [] -> false
     | hd' :: tl' -> (&&) (f hd hd') (forallb2 f tl tl'))

(** val coq_Forall_All : 'a1 list -> ('a1, __) coq_All **)

let rec coq_Forall_All = function
| [] -> All_nil
| y :: l0 -> All_cons (y, l0, __, (coq_Forall_All l0))

(** val forallb_All : ('a1 -> bool) -> 'a1 list -> ('a1, __) coq_All **)

let forallb_All _ =
  coq_Forall_All

(** val coq_All2_impl :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> 'a3 ->
    'a4) -> ('a1, 'a2, 'a4) coq_All2 **)

let rec coq_All2_impl _ _ a x =
  match a with
  | All2_nil -> All2_nil
  | All2_cons (x0, y, l, l', y0, a0) ->
    All2_cons (x0, y, l, l', (x x0 y y0), (coq_All2_impl l l' a0 x))

(** val coq_All_impl :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a3)
    coq_All **)

let rec coq_All_impl _ a x =
  match a with
  | All_nil -> All_nil
  | All_cons (x0, l, y, a0) ->
    All_cons (x0, l, (x x0 y), (coq_All_impl l a0 x))

(** val coq_Alli_impl :
    'a1 list -> nat -> ('a1, 'a2) coq_Alli -> (nat -> 'a1 -> 'a2 -> 'a3) ->
    ('a1, 'a3) coq_Alli **)

let rec coq_Alli_impl _ n x x0 =
  match x with
  | Alli_nil -> Alli_nil
  | Alli_cons (hd, tl, y, a) ->
    Alli_cons (hd, tl, (x0 n hd y), (coq_Alli_impl tl (S n) a x0))

(** val coq_All_map :
    ('a1 -> 'a2) -> 'a1 list -> ('a1, 'a3) coq_All -> ('a2, 'a3) coq_All **)

let rec coq_All_map f _ = function
| All_nil -> All_nil
| All_cons (x0, l, y, a) ->
  All_cons ((f x0),
    (let rec map = function
     | [] -> []
     | a0 :: t -> (f a0) :: (map t)
     in map l), y, (coq_All_map f l a))

(** val coq_All_map_inv :
    ('a1 -> 'a2) -> 'a1 list -> ('a2, 'a3) coq_All -> ('a1, 'a3) coq_All **)

let rec coq_All_map_inv f l hf =
  match l with
  | [] ->
    (match hf with
     | All_nil -> All_nil
     | All_cons (_, _, _, _) -> assert false (* absurd case *))
  | y :: l0 ->
    (match hf with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x, x0) ->
       All_cons (y, l0, x, (coq_All_map_inv f l0 x0)))

(** val coq_Alli_app :
    nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2)
    coq_Alli * ('a1, 'a2) coq_Alli **)

let rec coq_Alli_app n l l' =
  match l with
  | [] -> (fun h -> (Alli_nil, h))
  | y :: l0 ->
    let iHl = fun x x0 -> coq_Alli_app x l0 x0 in
    (fun h ->
    match h with
    | Alli_nil -> assert false (* absurd case *)
    | Alli_cons (_, _, x, x0) ->
      ((Alli_cons (y, l0, x,
        (let n0 = S n in let (x1, _) = iHl n0 l' x0 in x1))),
        (let n0 = S n in let (_, x1) = iHl n0 l' x0 in x1)))

(** val coq_Alli_nth_error :
    nat -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_Alli -> 'a2 **)

let rec coq_Alli_nth_error k _ i x = function
| Alli_nil -> assert false (* absurd case *)
| Alli_cons (_, tl, y, a) ->
  (match i with
   | O -> y
   | S n -> coq_Alli_nth_error (S k) tl n x a)

(** val forall_nth_error_Alli :
    nat -> 'a1 list -> (nat -> 'a1 -> __ -> 'a2) -> ('a1, 'a2) coq_Alli **)

let rec forall_nth_error_Alli k l h =
  match l with
  | [] -> Alli_nil
  | y :: l0 ->
    Alli_cons (y, l0, (h O y __),
      (forall_nth_error_Alli (S k) l0 (fun i x _ -> h (S i) x __)))

(** val coq_Alli_app_inv :
    'a1 list -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli
    -> ('a1, 'a2) coq_Alli **)

let rec coq_Alli_app_inv _ l' n x x0 =
  match x with
  | Alli_nil -> x0
  | Alli_cons (hd, tl, y, a) ->
    let iHX = coq_Alli_app_inv tl l' (S n) a x0 in
    Alli_cons (hd, (app tl l'), y, iHX)

(** val coq_Alli_rev_nth_error :
    'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_Alli -> 'a2 **)

let coq_Alli_rev_nth_error l n x x0 =
  let rec f l0 n0 x1 x2 =
    match l0 with
    | [] -> (fun _ -> assert false (* absurd case *))
    | y :: l1 ->
      let __top_assumption_ = coq_Alli_app O (rev l1) (y :: []) x2 in
      let _evar_0_ = fun alll alla ->
        match alla with
        | Alli_nil -> assert false (* absurd case *)
        | Alli_cons (_, _, x3, _) ->
          (match n0 with
           | O -> x3
           | S n1 -> f l1 n1 x1 alll __)
      in
      (fun _ -> let (a, b) = __top_assumption_ in _evar_0_ a b)
  in f l n x x0 __

type size = nat

(** val coq_All2_from_nth_error :
    'a1 list -> 'a2 list -> (nat -> 'a1 -> 'a2 -> __ -> __ -> __ -> 'a3) ->
    ('a1, 'a2, 'a3) coq_All2 **)

let rec coq_All2_from_nth_error l l2 x =
  match l with
  | [] ->
    (match l2 with
     | [] -> All2_nil
     | _ :: _ -> assert false (* absurd case *))
  | y :: l0 ->
    (match l2 with
     | [] -> assert false (* absurd case *)
     | b :: l1 ->
       All2_cons (y, b, l0, l1, (x O y b __ __ __),
         (coq_All2_from_nth_error l0 l1 (fun n x1 x2 _ _ _ ->
           x (S n) x1 x2 __ __ __))))

(** val coq_All2_prod :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a4)
    coq_All2 -> ('a1, 'a2, 'a3 * 'a4) coq_All2 **)

let rec coq_All2_prod _ _ a x =
  match a with
  | All2_nil ->
    (match x with
     | All2_nil -> All2_nil
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_cons (x0, y, l, l', y0, a0) ->
    (match x with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, x1, x2) ->
       All2_cons (x0, y, l, l', (y0, x1), (coq_All2_prod l l' a0 x2)))

(** val coq_All_prod_inv :
    'a1 list -> ('a1, 'a2 * 'a3) coq_All -> ('a1, 'a2) coq_All * ('a1, 'a3)
    coq_All **)

let rec coq_All_prod_inv _ = function
| All_nil -> (All_nil, All_nil)
| All_cons (x, l, y, a0) ->
  let (a1, a2) = coq_All_prod_inv l a0 in
  let (p, q) = y in ((All_cons (x, l, p, a1)), (All_cons (x, l, q, a2)))

(** val coq_All_prod :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a3) coq_All -> ('a1, 'a2 * 'a3)
    coq_All **)

let rec coq_All_prod _ a h2 =
  match a with
  | All_nil -> All_nil
  | All_cons (x, l, y, a0) ->
    (match h2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x0, x1) ->
       let iHh1 = coq_All_prod l a0 x1 in All_cons (x, l, (y, x0), iHh1))

type ('a, 'p) coq_All2_fold =
| All2_fold_nil
| All2_fold_cons of 'a * 'a * 'a list * 'a list * ('a, 'p) coq_All2_fold * 'p

type ('a, 'b, 'p) coq_All_over = 'p

(** val coq_All2_fold_impl :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list -> 'a1 list
    -> 'a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold **)

let rec coq_All2_fold_impl _ _ a x =
  match a with
  | All2_fold_nil -> All2_fold_nil
  | All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
    All2_fold_cons (d, d', _UU0393_, _UU0393_',
      (coq_All2_fold_impl _UU0393_ _UU0393_' a0 x),
      (x _UU0393_ _UU0393_' d d' y))

(** val coq_All2_fold_prod :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a3)
    coq_All2_fold -> ('a1, 'a2 * 'a3) coq_All2_fold **)

let rec coq_All2_fold_prod _ _ a h =
  match a with
  | All2_fold_nil ->
    let h0 = ([],[]),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_fold_nil -> All2_fold_nil
     | All2_fold_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
    let h0 = ((d :: _UU0393_),(d' :: _UU0393_')),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_fold_nil -> assert false (* absurd case *)
     | All2_fold_cons (_, _, _, _, a1, q) ->
       All2_fold_cons (d, d', _UU0393_, _UU0393_',
         (coq_All2_fold_prod _UU0393_ _UU0393_' a0 a1), (y, q)))

(** val coq_All_eta3 :
    (('a1 * 'a2) * 'a3) list -> ((('a1 * 'a2) * 'a3, __) coq_All,
    (('a1 * 'a2) * 'a3, 'a4) coq_All) iffT **)

let coq_All_eta3 ls =
  ((fun x ->
    let rec f _ = function
    | All_nil -> All_nil
    | All_cons (x0, l, y, a0) -> All_cons (x0, l, (Obj.magic y), (f l a0))
    in f ls x), (fun x ->
    let rec f _ = function
    | All_nil -> All_nil
    | All_cons (x0, l, y, a0) -> All_cons (x0, l, (Obj.magic y), (f l a0))
    in f ls x))

(** val coq_All_All2_swap_sum :
    'a3 list -> 'a1 list -> 'a2 list -> ('a3, ('a1, 'a2, 'a4) coq_All2)
    coq_All -> (__, ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2) sum **)

let rec coq_All_All2_swap_sum l ls2 ls3 x =
  match l with
  | [] ->
    (match ls2 with
     | [] ->
       (match ls3 with
        | [] ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | _ :: _ ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *)))
     | _ :: _ ->
       (match ls3 with
        | [] ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | _ :: _ ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))))
  | y :: l0 ->
    (match ls2 with
     | [] ->
       (match ls3 with
        | [] ->
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x0, _) ->
             (match x0 with
              | All2_nil -> Coq_inr All2_nil
              | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *)))
        | _ :: _ -> assert false (* absurd case *))
     | a :: l1 ->
       (match ls3 with
        | [] -> assert false (* absurd case *)
        | b :: l2 ->
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x0, x1) ->
             (match x0 with
              | All2_nil -> assert false (* absurd case *)
              | All2_cons (_, _, _, _, x2, x3) ->
                Coq_inr (All2_cons (a, b, l1, l2, (All_cons (y, l0, x2,
                  (coq_All_impl l0 x1 (fun _ x4 ->
                    match x4 with
                    | All2_nil -> assert false (* absurd case *)
                    | All2_cons (_, _, _, _, x5, _) -> x5)))),
                  (coq_All2_impl l1 l2
                    (coq_All2_prod l1 l2 x3
                      (let s =
                         coq_All_All2_swap_sum l0 l1 l2
                           (coq_All_impl l0 x1 (fun _ x4 ->
                             match x4 with
                             | All2_nil -> assert false (* absurd case *)
                             | All2_cons (_, _, _, _, _, x5) -> x5))
                       in
                       match s with
                       | Coq_inl _ ->
                         (match x1 with
                          | All_nil ->
                            coq_All2_impl l1 l2 x3 (fun _ _ _ -> All_nil)
                          | All_cons (_, _, _, _) ->
                            assert false (* absurd case *))
                       | Coq_inr a0 -> a0)) (fun _ _ x4 ->
                    let (y0, y1) = x4 in All_cons (y, l0, y0, y1)))))))))

(** val coq_All_All2_swap :
    'a3 list -> 'a1 list -> 'a2 list -> ('a3, ('a1, 'a2, 'a4) coq_All2)
    coq_All -> ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2 **)

let coq_All_All2_swap ls1 ls2 ls3 x =
  match ls1 with
  | [] -> coq_All2_from_nth_error ls2 ls3 (fun _ _ _ _ _ _ -> All_nil)
  | c :: l ->
    let rec f l0 ls4 ls5 x0 =
      match l0 with
      | [] ->
        (match ls4 with
         | [] ->
           (match ls5 with
            | [] ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_nil ->
                    (match x2 with
                     | All_nil -> All2_nil
                     | All_cons (_, _, _, _) -> assert false (* absurd case *))
                  | All2_cons (_, _, _, _, _, _) ->
                    assert false (* absurd case *)))
            | _ :: _ -> assert false (* absurd case *))
         | a :: l1 ->
           (match ls5 with
            | [] -> assert false (* absurd case *)
            | b :: l2 ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_nil -> assert false (* absurd case *)
                  | All2_cons (_, _, _, _, x3, x4) ->
                    (match x2 with
                     | All_nil ->
                       All2_cons (a, b, l1, l2, (All_cons (c, [], x3,
                         All_nil)),
                         (coq_All2_impl l1 l2 x4 (fun _ _ x5 -> All_cons (c,
                           [], x5, All_nil))))
                     | All_cons (_, _, _, _) -> assert false (* absurd case *))))))
      | y :: l1 ->
        (match ls4 with
         | [] ->
           (match ls5 with
            | [] ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_nil ->
                    (match x2 with
                     | All_nil -> assert false (* absurd case *)
                     | All_cons (_, _, x3, _) ->
                       (match x3 with
                        | All2_nil -> All2_nil
                        | All2_cons (_, _, _, _, _, _) ->
                          assert false (* absurd case *)))
                  | All2_cons (_, _, _, _, _, _) ->
                    assert false (* absurd case *)))
            | _ :: _ -> assert false (* absurd case *))
         | a :: l2 ->
           (match ls5 with
            | [] -> assert false (* absurd case *)
            | b :: l3 ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_nil -> assert false (* absurd case *)
                  | All2_cons (_, _, _, _, x3, x4) ->
                    (match x2 with
                     | All_nil -> assert false (* absurd case *)
                     | All_cons (_, _, x5, x6) ->
                       (match x5 with
                        | All2_nil -> assert false (* absurd case *)
                        | All2_cons (_, _, _, _, x7, x8) ->
                          All2_cons (a, b, l2, l3, (All_cons (c, (y :: l1),
                            x3, (All_cons (y, l1, x7,
                            (coq_All_impl l1 x6 (fun _ x9 ->
                              match x9 with
                              | All2_nil -> assert false (* absurd case *)
                              | All2_cons (_, _, _, _, x10, _) -> x10)))))),
                            (coq_All2_impl l2 l3
                              (coq_All2_prod l2 l3 x4
                                (coq_All2_impl l2 l3
                                  (coq_All2_prod l2 l3 x8
                                    (coq_All2_impl l2 l3
                                      (f l1 l2 l3 (All_cons (c, l1, x4,
                                        (coq_All_impl l1 x6 (fun _ x9 ->
                                          match x9 with
                                          | All2_nil ->
                                            assert false (* absurd case *)
                                          | All2_cons (_, _, _, _, _, x10) ->
                                            x10))))) (fun _ _ x9 ->
                                      match x9 with
                                      | All_nil ->
                                        assert false (* absurd case *)
                                      | All_cons (_, _, _, x10) -> x10)))
                                  (fun _ _ x9 ->
                                  let (y0, y1) = x9 in
                                  All_cons (y, l1, y0, y1)))) (fun _ _ x9 ->
                              let (y0, y1) = x9 in
                              All_cons (c, (y :: l1), y0, y1))))))))))
    in f l ls2 ls3 x

(** val coq_All_All2_fold_swap_sum :
    'a2 list -> 'a1 list -> 'a1 list -> ('a2, ('a1, 'a3) coq_All2_fold)
    coq_All -> (__, ('a1, ('a2, 'a3) coq_All) coq_All2_fold) sum **)

let rec coq_All_All2_fold_swap_sum l ls2 ls3 x =
  match l with
  | [] ->
    (match ls2 with
     | [] ->
       (match ls3 with
        | [] ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | _ :: _ ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *)))
     | _ :: _ ->
       (match ls3 with
        | [] ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | _ :: _ ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))))
  | y :: l0 ->
    (match ls2 with
     | [] ->
       (match ls3 with
        | [] ->
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x0, _) ->
             (match x0 with
              | All2_fold_nil -> Coq_inr All2_fold_nil
              | All2_fold_cons (_, _, _, _, _, _) ->
                assert false (* absurd case *)))
        | _ :: _ -> assert false (* absurd case *))
     | a :: l1 ->
       (match ls3 with
        | [] -> assert false (* absurd case *)
        | a0 :: l2 ->
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x0, x1) ->
             (match x0 with
              | All2_fold_nil -> assert false (* absurd case *)
              | All2_fold_cons (_, _, _, _, x2, x3) ->
                Coq_inr (All2_fold_cons (a, a0, l1, l2,
                  (coq_All2_fold_impl l1 l2
                    (coq_All2_fold_prod l1 l2 x2
                      (let s =
                         coq_All_All2_fold_swap_sum l0 l1 l2
                           (coq_All_impl l0 x1 (fun _ x4 ->
                             match x4 with
                             | All2_fold_nil -> assert false (* absurd case *)
                             | All2_fold_cons (_, _, _, _, x5, _) -> x5))
                       in
                       match s with
                       | Coq_inl _ ->
                         (match x1 with
                          | All_nil ->
                            coq_All2_fold_impl l1 l2 x2 (fun _ _ _ _ _ ->
                              All_nil)
                          | All_cons (_, _, _, _) ->
                            assert false (* absurd case *))
                       | Coq_inr a1 -> a1)) (fun _ _ _ _ x4 ->
                    let (y0, y1) = x4 in All_cons (y, l0, y0, y1))),
                  (All_cons (y, l0, x3,
                  (coq_All_impl l0 x1 (fun _ x4 ->
                    match x4 with
                    | All2_fold_nil -> assert false (* absurd case *)
                    | All2_fold_cons (_, _, _, _, _, x5) -> x5))))))))))
