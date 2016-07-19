Require Export Stlc.SpecSyntax.
Require Export Stlc.SpecEvaluation.
Require Export Stlc.LemmasSyntaxBasic.
Require Export Coq.Program.Tactics.

(* ** Evaluation contexts *)
Lemma ectx_cat (C₁ C₂: PCtx) :
  ECtx C₁ → ECtx C₂ → ECtx (pctx_cat C₁ C₂).
Proof.
  induction C₂; simpl; intros; destruct_conjs; auto.
Qed.

Lemma evalstar_ctx C t t' (eC: ECtx C) :
  t -->* t' → pctx_app t C -->* pctx_app t' C.
Proof. induction 1; eauto using eval with eval. Qed.

Lemma evalplus_ctx C t t' (eC: ECtx C) :
  t -->+ t' → pctx_app t C -->+ pctx_app t' C.
Proof. induction 1; eauto using eval with eval. Qed.


(* ** Transitive and transitive-reflexive closure *)
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

Lemma inversion_evalStar {t t'} :
  t -->* t' → t = t' ∨ (t -->+ t').
Proof. inversion 1; eauto using evalPlusStarToPlus with eval. Qed.


(* Termination and divergene *)
Lemma inversion_termination_app₁ {t₁ t₂} :
  (app t₁ t₂)⇓ → t₁⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (papp₁ phole t₂)); simpl; eauto.
Qed.

Lemma inversion_termination_app₂ {t₁ t₂} :
  Value t₁ → (app t₁ t₂)⇓ → t₂⇓.
Proof.
  intros v₁ nr.
  depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (papp₂ t₁ phole)); simpl; eauto.
Qed.

(* Lemma inversion_termination_app₂' {t₁ τ₁ t₂} : *)
(*   ⟪ empty ⊢ t₁ : τ₁ ⟫ → (app t₁ t₂)⇓ → t₂⇓. *)
(* Proof. *)
(*   intros wt₁ nr. *)
(*   destruct (termination_value wt₁) as (t₁' & ? & ?). *)
(*   eapply (inversion_termination_app₁ nr). *)
(*   eapply inversion_termination_app₂; eauto. *)
(*   assert (app t₁ t₂ -->* app t₁' t₂) *)
(*     by (eapply (evalstar_ctx (papp₁ phole t₂)); simpl; auto). *)
(*   eapply (termination_closed_under_evalstar H1); auto. *)
(* Qed. *)

Lemma inversion_termination_ite₁ {t₁ t₂ t₃} :
  (ite t₁ t₂ t₃)⇓ → t₁⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (pite₁ phole t₂ t₃)); simpl; eauto.
Qed.

Lemma inversion_termination_pair₁ {t₁ t₂} :
  (pair t₁ t₂)⇓ → t₁⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (ppair₁ phole t₂)); simpl; eauto.
Qed.

Lemma inversion_termination_pair₂ {t₁ t₂} :
  Value t₁ → (pair t₁ t₂)⇓ → t₂⇓.
Proof.
  intros v₁ nr.
  depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (ppair₂ t₁ phole)); simpl; eauto.
Qed.

Lemma inversion_termination_proj₁ {t} :
  (proj₁ t)⇓ → t⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (pproj₁ phole)); simpl; eauto.
Qed.

Lemma inversion_termination_proj₂ {t} :
  (proj₂ t)⇓ → t⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (pproj₂ phole)); simpl; eauto.
Qed.

Lemma inversion_termination_inl {t} :
  (inl t)⇓ → t⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (pinl phole)); simpl; eauto.
Qed.

Lemma inversion_termination_inr {t} :
  (inr t)⇓ → t⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (pinr phole)); simpl; eauto.
Qed.

Lemma inversion_termination_caseof₁ {t₁ t₂ t₃} :
  (caseof t₁ t₂ t₃)⇓ → t₁⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (pcaseof₁ phole t₂ t₃)); simpl; eauto.
Qed.

Lemma inversion_termination_seq₁ {t₁ t₂} :
  (seq t₁ t₂)⇓ → t₁⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (pseq₁ phole t₂)); simpl; eauto.
Qed.

Lemma inversion_termination_fixt {τ₁ τ₂ t} :
  (fixt τ₁ τ₂ t)⇓ → t⇓.
Proof.
  intro nr. depind nr.
  constructor; intros.
  eapply H0; eauto.
  eapply (eval_ctx (pfixt τ₁ τ₂ phole)); simpl; eauto.
Qed.

Lemma inversion_termination_evalcontext :
  ∀ C t, ECtx C → Terminating (pctx_app t C) → Terminating t.
Proof.
  induction C; crush; destruct_conjs;
  try match goal with
        | [ H: False |- _ ] => destruct H
      end.
  - eauto using inversion_termination_app₁.
  - eauto using inversion_termination_app₂.
  - eauto using inversion_termination_ite₁.
  - eauto using inversion_termination_pair₁.
  - eauto using inversion_termination_pair₂.
  - eauto using inversion_termination_proj₁.
  - eauto using inversion_termination_proj₂.
  - eauto using inversion_termination_inl.
  - eauto using inversion_termination_inr.
  - eauto using inversion_termination_caseof₁.
  - eauto using inversion_termination_seq₁.
  - eauto using inversion_termination_fixt.
Qed.

Lemma termination_closed_under_evalplus {t t'} :
  t -->+ t' → t⇓ → t'⇓.
Proof. intros e m; induction e; inversion m; auto. Qed.

Lemma termination_closed_under_evalstar {t t'} :
  t -->* t' → t⇓ → t'⇓.
Proof.
  intros e; destruct (inversion_evalStar e); subst;
    eauto using termination_closed_under_evalplus.
Qed.

Corollary divergence_closed_under_eval {t t'} :
  t --> t' → t'⇑ → t⇑.
Proof. eauto using TerminatingD with eval. Qed.

Corollary divergence_closed_under_evalplus {t t'} :
  t -->+ t' → t'⇑ → t⇑.
Proof. eauto using termination_closed_under_evalplus. Qed.

Corollary divergence_closed_under_evalstar {t t'} :
  t -->* t' → t'⇑ → t⇑.
Proof. eauto using termination_closed_under_evalstar. Qed.

Corollary divergence_closed_under_evalcontex t :
  t⇑ → ∀ p, ECtx p → (pctx_app t p)⇑.
Proof. eauto using inversion_termination_evalcontext. Qed.

(* Stronger induction principle *)
Lemma Terminating_ind' (P: Tm → Prop)
 (step: ∀ t,
   (∀ t', t -->+ t' → t'⇓) →
   (∀ t', t -->+ t' → P t') → P t) :
  ∀ t, t⇓ → P t.
Proof.
  pose proof @termination_closed_under_evalplus.
  intros t m.
  apply step; eauto.
  induction m; inversion 1; eauto.
Qed.

Lemma cycles_dont_terminate {t} :
  t -->+ t → t⇑.
Proof. induction 2 using Terminating_ind'; eauto. Qed.

(* Local Variables: *)
(* coq-load-path: (("." "Stlc")) *)
(* End: *)
