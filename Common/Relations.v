Require Export Coq.Relations.Relations.
Require Export Coq.Unicode.Utf8.

Hint Constructors clos_refl_trans_1n : eval.
Hint Constructors clos_trans_1n : eval.

(* ** Transitive and transitive-reflexive closure *)
Section RtProperties.

  Context {A: Type}.
  Context {R: relation A}.

  Notation "t₁ --> t₂" := (R t₁ t₂) (at level 80).
  Notation "t₁ -->* t₂" := (clos_refl_trans_1n A R t₁ t₂) (at level 80).
  Notation "t₁ -->+ t₂" := (clos_trans_1n A R t₁ t₂) (at level 80).

  Lemma evalToPlus {t t'} : t --> t' -> t -->+ t'.
  Proof. eauto with eval. Qed.

  Lemma evalToStar {t t'} : t --> t' -> t -->* t'.
  Proof. eauto with eval. Qed.

  Lemma evalPlusToStar {t t'} : t -->+ t' -> t -->* t'.
  Proof. induction 1; eauto with eval. Qed.

  Lemma evalStarPlusToPlus {t t' t''} :
    t -->* t' → t' -->+ t'' → t -->+ t''.
  Proof. induction 1; eauto with eval. Qed.

  Lemma evalPlusStepToPlus {t t' t''} :
    t -->+ t' → t' --> t'' → t -->+ t''.
  Proof. induction 1; eauto with eval. Qed.

  Lemma evalPlusStarToPlus {t t' t''} :
    t -->+ t' → t' -->* t'' → t -->+ t''.
  Proof. induction 2; eauto using evalPlusStepToPlus with eval. Qed.

  Lemma evalStepStarToPlus {t} t' {t''} :
    t --> t' → t' -->* t'' → t -->+ t''.
  Proof. eauto using evalPlusStarToPlus with eval. Qed.

  Lemma evalStepStar {t} t' {t''} :
    t --> t' → t' -->* t'' → t -->* t''.
  Proof. eauto with eval. Qed.

  Lemma inversion_evalStar {t t'} :
    t -->* t' → t = t' ∨ (t -->+ t').
  Proof. inversion 1; eauto using evalPlusStarToPlus with eval. Qed.

End RtProperties.

Section StepRel.

  Inductive stepRel {A} (R : A → A → Prop) (t : A) : A → nat → Prop :=
  | stepRel_zero : stepRel R t t 0
  | stepRel_step : forall t' t'' n, R t t' → stepRel R t' t'' n → stepRel R t t'' (S n).

End StepRel.