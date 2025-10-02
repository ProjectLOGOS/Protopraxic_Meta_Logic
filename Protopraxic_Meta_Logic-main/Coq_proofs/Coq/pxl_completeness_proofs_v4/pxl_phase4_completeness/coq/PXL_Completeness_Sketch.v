From Coq Require Import Logic.Classical.

Section Deep.

Inductive form : Type :=
| Bot  : form
| Var  : nat -> form
| Impl : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Neg  : form -> form
| Box  : form -> form
| Dia  : form -> form.

Inductive Prov : form -> Prop :=
| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
| ax_T  : forall p,   Prov (Impl (Box p) p)
| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))
| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))
| ax_PL_imp : forall p q r,
    Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)
| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)
| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)
| ax_PL_em  : forall p, Prov (Or p (Neg p))
| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q
| nec   : forall p, Prov p -> Prov (Box p).

Record frame := {
  W : Type; R : W -> W -> Prop;
  R_refl  : forall w, R w w;
  R_symm  : forall w u, R w u -> R u w;
  R_trans : forall w u v, R w u -> R u v -> R w v
}.

Definition valuation (F:frame) := nat -> (W F) -> Prop.

Fixpoint eval (F:frame) (v:valuation F) (w:(W F)) (φ:form) : Prop :=
  match φ with
  | Bot      => False
  | Var n    => v n w
  | Impl p q => eval F v w p -> eval F v w q
  | And p q  => eval F v w p /\ eval F v w q
  | Or p q   => eval F v w p \/ eval F v w q
  | Neg p    => ~ eval F v w p
  | Box p    => forall u, R F w u -> eval F v u p
  | Dia p    => exists u, R F w u /\ eval F v u p
  end.

Definition valid_on (F:frame) (φ:form) : Prop := forall v w, eval F v w φ.
Definition valid (φ:form) : Prop := forall (F:frame), valid_on F φ.

Definition set := form -> Prop.
Definition consistent (Γ:set) : Prop := ~ (exists p, Γ p /\ Γ (Neg p)).
Definition extends (Γ Δ:set) : Prop := forall p, Γ p -> Δ p.
Definition maximal (Γ:set) : Prop :=
  consistent Γ /\ forall p, Γ p \/ Γ (Neg p).

Axiom lindenbaum : forall Γ, consistent Γ -> exists Δ, extends Γ Δ /\ maximal Δ.

Definition In (Γ:set) (p:form) : Prop := Γ p.

Definition can_world := { Γ : set | maximal Γ }.

Definition can_R (w u:can_world) : Prop :=
  forall p, In (proj1_sig w) (Box p) -> In (proj1_sig u) p.

Definition can_frame : frame.
Proof.
  refine {| W := can_world; R := can_R |}.
  - admit.
  - admit.
  - admit.
Defined.

Fixpoint forces (w:can_world) (p:form) : Prop :=
  match p with
  | Bot => False
  | Var n => True
  | Impl a b => forces w a -> forces w b
  | And a b => forces w a /\ forces w b
  | Or a b  => forces w a \/ forces w b
  | Neg a   => ~ forces w a
  | Box a   => forall u, can_R w u -> forces u a
  | Dia a   => exists u, can_R w u /\ forces u a
  end.

Theorem truth_lemma : forall (w:can_world) p, In (proj1_sig w) p <-> forces w p.
Admitted.

Theorem weak_completeness : forall p, (forall (F:frame), valid_on F p) -> Prov p.
Admitted.

End Deep.
