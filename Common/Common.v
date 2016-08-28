Require Export Coq.Unicode.Utf8.
Require Import Omega.

Lemma S_le {n m} : S n ≤ m → exists m', m = S m' ∧ n ≤ m'.
Proof.
  intros le; destruct m; [exfalso|exists m]; omega.
Qed.

Inductive stepRel {A} (R : A → A → Prop) (t : A) : A → nat → Prop :=
| stepRel_zero : stepRel R t t 0
| stepRel_step : forall t' t'' n, R t t' → stepRel R t' t'' n → stepRel R t t'' (S n).
