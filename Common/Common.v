Require Export Coq.Unicode.Utf8.
Require Import Omega.

Lemma S_le {n m} : S n ≤ m → exists m', m = S m' ∧ n ≤ m'.
Proof.
  intros le; destruct m; [exfalso|exists m]; omega.
Qed.
