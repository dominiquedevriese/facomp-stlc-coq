Require Export Stlc.Inst.
Require Export Coq.Relations.Relation_Operators.

(** ** Evaluation *)

Fixpoint Value (t: Tm) : Prop :=
  match t with
    | abs τ t      => True
    | unit         => True
    | true         => True
    | false        => True
    | pair t₁ t₂   => Value t₁ ∧ Value t₂
    | inl t        => Value t
    | inr t        => Value t
    | var _ | app _ _ | ite _ _ _
    | proj₁ _ | proj₂ _ | caseof _ _ _
    | seq _ _ | fixt _ _ _   => False
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
    | pfixt τ₁ τ₂ C    => ECtx C
    | pabs _ _ | pite₂ _ _ _ | pite₃ _ _ _
    | pcaseof₂ _ _ _ | pcaseof₃ _ _ _
    | pseq₂ _ _ => False
  end.

Reserved Notation "t₁ --> t₂" (at level 80).
Inductive eval : Tm → Tm → Prop :=
  | eval_ctx C {t t'} :
      t --> t' → ECtx C → pctx_app t C --> pctx_app t' C
  | eval_beta {τ₁ t₁ t₂} :
      Value t₂ →
      app (abs τ₁ t₁) t₂ --> subst0 t₂ t₁
  | eval_ite_true {t₁ t₂} :
      ite true t₁ t₂ --> t₁
  | eval_ite_false {t₁ t₂} :
      ite false t₁ t₂ --> t₂
  | eval_proj₁ {t₁ t₂} :
      Value t₁ → Value t₂ →
      proj₁ (pair t₁ t₂) --> t₁
  | eval_proj₂ {t₁ t₂} :
      Value t₁ → Value t₂ →
      proj₂ (pair t₁ t₂) --> t₂
  | eval_case_inl {t t₁ t₂} :
      Value t →
      caseof (inl t) t₁ t₂ --> subst0 t t₁
  | eval_case_inr {t t₁ t₂} :
      Value t →
      caseof (inr t) t₁ t₂ --> subst0 t t₂
  | eval_seq_next {t₁ t₂} :
      Value t₁ →
      seq t₁ t₂ --> t₂
  | eval_fix {τ₁ τ₂ t} :
      fixt τ₁ τ₂ (abs (τ₁ ⇒ τ₂) t) -->
      subst0 (abs τ₁ (app (fixt τ₁ τ₂ (abs (τ₁ ⇒ τ₂) t[wkm↑])) (var 0))) t
where "t₁ --> t₂" := (eval t₁ t₂).

Inductive Terminating (t: Tm) : Prop :=
  | TerminatingI : (∀ t', t --> t' → Terminating t') → Terminating t.
Notation "t ⇓" := (Terminating t) (at level 8, format "t ⇓").

Lemma TerminatingD (t: Tm) (m: t⇓) :
  ∀ t', t --> t' → Terminating t'.
Proof. inversion m; auto. Qed.

Notation "t ⇑" := (not (Terminating t)) (at level 8, format "t ⇑").
Notation "t₁ -->* t₂" := (clos_refl_trans_1n Tm eval t₁ t₂) (at level 80).
Notation "t₁ -->+ t₂" := (clos_trans_1n Tm eval t₁ t₂) (at level 80).

Hint Constructors eval : eval.
Hint Constructors clos_refl_trans_1n : eval.
Hint Constructors clos_trans_1n : eval.
