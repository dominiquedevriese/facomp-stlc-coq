Require Export Coq.Unicode.Utf8.
Require Import Omega.

Lemma S_le {n m} : S n ≤ m → exists m', m = S m' ∧ n ≤ m'.
Proof.
  intros le; destruct m; [exfalso|exists m]; omega.
Qed.

Lemma lt_inv_plus {n m} : n < m → exists r, m = n + S r.
Proof.
  induction 1.
  - exists 0; omega.
  - destruct IHle as [r ?]; subst.
    exists (S r); omega.
Qed.

Lemma le_inv_plus {n m} : n ≤ m → exists r, m = n + r.
Proof.
  induction 1.
  - exists 0; omega.
  - destruct IHle as [r ?]; subst.
    exists (S r); omega.
Qed.

