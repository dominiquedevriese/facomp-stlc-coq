Require Export Utlc.Inst.
Require Export Coq.Relations.Relation_Operators.

(** ** Evaluation *)

Fixpoint Value (t: UTm) : Prop :=
  match t with
    | wrong        => False
    | abs t        => True
    | unit         => True
    | true         => True
    | false        => True
    | pair t₁ t₂   => Value t₁ ∧ Value t₂
    | inl t        => Value t
    | inr t        => Value t
    | var _ | app _ _ | ite _ _ _
    | proj₁ _ | proj₂ _ | caseof _ _ _
    | seq _ _  => False
  end.

Fixpoint ECtx (C: PCtx) : Prop :=
  match C with
    | phole            => True
    | papp₁ C t        => ECtx C
    | papp₂ t C        => Value t ∧ ECtx C
    | pite₁ C t₂ t₃    => ECtx C
    | ppair₁ C t       => ECtx C
    | ppair₂ t C       => Value t ∧ ECtx C
    | pproj₁ C         => ECtx C
    | pproj₂ C         => ECtx C
    | pinl C           => ECtx C
    | pinr C           => ECtx C
    | pcaseof₁ C t₂ t₃ => ECtx C
    | pseq₁ C t        => ECtx C
    | pabs _ | pite₂ _ _ _ | pite₃ _ _ _
    | pcaseof₂ _ _ _ | pcaseof₃ _ _ _
    | pseq₂ _ _ => False
  end.

Reserved Notation "t₁ -->₀ t₂" (at level 80).
Inductive eval₀ : UTm → UTm → Prop :=
  | eval_beta_wrong {t₁ t₂} :
      Value t₁ → Value t₂ →
      (∀ t,  t₁ ≠ abs t) →
      app t₁ t₂ -->₀ wrong
  | eval_beta {t₁ t₂} :
      Value t₂ →
      app (abs t₁) t₂ -->₀ t₁[beta1 t₂]
  | eval_ite_wrong {t₁ t₂ t₃} :
      Value t₁ → t₁ ≠ true  → t₁ ≠ false →
      ite t₁ t₂ t₃ -->₀ wrong
  | eval_ite_true {t₁ t₂} :
      ite true t₁ t₂ -->₀ t₁
  | eval_ite_false {t₁ t₂} :
      ite false t₁ t₂ -->₀ t₂
  | eval_proj₁_wrong {t} :
      Value t →
      (∀ t₁ t₂, t ≠ pair t₁ t₂) →
      proj₁ t -->₀ wrong
  | eval_proj₁ {t₁ t₂} :
      Value t₁ → Value t₂ →
      proj₁ (pair t₁ t₂) -->₀ t₁
  | eval_proj₂_wrong {t} :
      Value t →
      (∀ t₁ t₂, t ≠ pair t₁ t₂) →
      proj₂ t -->₀ wrong
  | eval_proj₂ {t₁ t₂} :
      Value t₁ → Value t₂ →
      proj₂ (pair t₁ t₂) -->₀ t₂
  | eval_case_wrong {t t₁ t₂} :
      Value t →
      (∀ t', t ≠ inl t') →
      (∀ t', t ≠ inr t') →
      caseof t t₁ t₂ -->₀ wrong
  | eval_case_inl {t t₁ t₂} :
      Value t →
      caseof (inl t) t₁ t₂ -->₀ t₁[beta1 t]
  | eval_case_inr {t t₁ t₂} :
      Value t →
      caseof (inr t) t₁ t₂ -->₀ t₂[beta1 t]
  | eval_seq_next {t₂} :
      seq unit t₂ -->₀ t₂
  | eval_seq_wrong {t₁ t₂} :
      Value t₁ →
      t₁ ≠ unit →
      seq t₁ t₂ -->₀ wrong
where "t₁ -->₀ t₂" := (eval₀ t₁ t₂).

Reserved Notation "t₁ --> t₂" (at level 80).
Inductive eval : UTm → UTm → Prop :=
  | eval_ctx₀ C {t t'} :
      t -->₀ t' → ECtx C → pctx_app t C --> pctx_app t' C
  | eval_ctx_wrong₀ C :
      ECtx C → C ≠ phole →
      pctx_app wrong C --> wrong
where "t₁ --> t₂" := (eval t₁ t₂).

Section DerivedRules.

  Lemma eval_eval₀ {t t'} : t -->₀ t' -> t --> t'.
  Proof. intro r; now apply (eval_ctx₀ phole r). Qed.

  Lemma eval_beta'' {t₁ t₂ t'} :
    Value t₂ → t' = t₁[beta1 t₂] →
    app (abs t₁) t₂ -->₀ t'.
  Proof. intros; subst; auto using eval₀. Qed.

  Lemma eval_beta' {t₁ t₂ t'} :
    Value t₂ → t' = t₁[beta1 t₂] →
    app (abs t₁) t₂ --> t'.
  Proof. intros; apply eval_eval₀; subst; auto using eval₀. Qed.

  Lemma eval₀_case_inl' {t t₁ t₂ t'} :
    Value t → t' = t₁[beta1 t] →
    caseof (inl t) t₁ t₂ -->₀ t'.
  Proof. intros; subst; auto using eval₀. Qed.

  Lemma eval₀_case_inr' {t t₁ t₂ t'} :
    Value t → t' = t₂[beta1 t] →
    caseof (inr t) t₁ t₂ -->₀ t'.
  Proof. intros; subst; auto using eval₀. Qed.

  Lemma eval_case_inl' {t t₁ t₂ t'} :
    Value t → t' = t₁[beta1 t] →
    caseof (inl t) t₁ t₂ --> t'.
  Proof. intros; apply eval_eval₀; subst; auto using eval₀. Qed.

  Lemma eval_case_inr' {t t₁ t₂ t'} :
    Value t → t' = t₂[beta1 t] →
    caseof (inr t) t₁ t₂ --> t'.
  Proof. intros; apply eval_eval₀; subst; auto using eval₀. Qed.

End DerivedRules.

Hint Resolve eval_beta' : eval.
Hint Resolve eval_case_inl' : eval.
Hint Resolve eval_case_inr' : eval.

Inductive Terminating (t: UTm) : Prop :=
  | TerminatingI : (∀ t', t --> t' → Terminating t') → Terminating t.
Notation "t ⇓" := (Terminating t) (at level 8, format "t ⇓").

Lemma TerminatingD (t: UTm) (m: t⇓) :
  ∀ t', t --> t' → Terminating t'.
Proof. inversion m; auto. Qed.

Notation "t ⇑" := (not (Terminating t)) (at level 8, format "t ⇑").
Notation "t₁ -->* t₂" := (clos_refl_trans_1n UTm eval t₁ t₂) (at level 80).
Notation "t₁ -->+ t₂" := (clos_trans_1n UTm eval t₁ t₂) (at level 80).

Hint Constructors eval₀ : eval.
Hint Constructors eval : eval.
Hint Constructors clos_refl_trans_1n : eval.
Hint Constructors clos_trans_1n : eval.

Definition normal (t : UTm) := ∀ t', ¬ (t --> t').

(* Terminates in maximum n steps *)
Inductive TerminatingN (t: UTm) : nat -> Prop :=
  | TerminatingIV : forall n, Value t -> TerminatingN t n
  | TerminatingIS : forall n, (∀ t', t --> t' → TerminatingN t' n) → TerminatingN t (S n).
Notation "t ⇓_ n" := (TerminatingN t n) (at level 8, format "t ⇓_ n").

Inductive evaln (t : UTm) : UTm → nat → Prop :=
| evaln_zero : evaln t t 0
| evaln_step : forall t' t'' n, t --> t' → evaln t' t'' n → evaln t t'' (S n).


Ltac crushUtlcEvaluationMatchH :=
  match goal with
    | [ H: exists tub', ?tu = abs tub' |- Value ?tu ] => (destruct H as [? ?]; subst)
  end.