Require Export Db.Lemmas.
Require Export Stlc.SpecSyntax.
Require Export Stlc.SpecEvaluation.
Require Export Coq.Program.Tactics.

(* ** Evaluation contexts *)
Lemma ectx_cat (C₁ C₂: PCtx) :
  ECtx C₁ → ECtx C₂ → ECtx (pctx_cat C₁ C₂).
Proof.
  induction C₂; simpl; intros; destruct_conjs; auto.
Qed.

Lemma pctx_cat_app (t : Tm) (C₁ C₂ : PCtx) :
  pctx_app t (pctx_cat C₁ C₂) = pctx_app (pctx_app t C₁) C₂.
Proof.
  induction C₂; crushStlc.
Qed.

Lemma eval_ctx C t t' (eC : ECtx C) :
  t --> t' -> pctx_app t C --> pctx_app t' C.
Proof.
  induction 1.
  rewrite <- ?pctx_cat_app in *.
  eauto using ectx_cat with eval.
Qed.

Lemma evalstar_ctx C t t' (eC: ECtx C) :
  t -->* t' → pctx_app t C -->* pctx_app t' C.
Proof. 
  induction 1 as [|t t'' t' e1 es IHes].
  - eauto with eval. 
  - enough (pctx_app t C --> pctx_app t'' C) by eauto with eval.
    apply eval_ctx; assumption.
Qed.

Lemma evalplus_ctx C t t' (eC: ECtx C) :
  t -->+ t' → pctx_app t C -->+ pctx_app t' C.
Proof. 
  induction 1 as [t t' e1|t t'' t' e1 es IHes];
  [enough (pctx_app t C --> pctx_app t' C) by eauto with eval|
   enough (pctx_app t C --> pctx_app t'' C) by eauto with eval];
  apply eval_ctx; assumption.
Qed.

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

Lemma inversion_termination_evalcontext_help :
  ∀ C t t', ECtx C → Terminating t' -> t' = pctx_app t C → Terminating t.
Proof.
  intros C t t' ecC term.
  revert t.
  depind term.
  intros t0 eq.
  constructor; intros t0' e.
  subst.
  assert (e' : pctx_app t0 C --> pctx_app t0' C) by (apply eval_ctx; assumption).
  refine (H0 _ e' _ eq_refl).
Qed.

Lemma inversion_termination_evalcontext :
  ∀ C t, ECtx C → Terminating (pctx_app t C) → Terminating t.
Proof.
  intros C t ec term.
  refine (inversion_termination_evalcontext_help C t _ ec term eq_refl). 
Qed.

(* Termination and divergene *)
Lemma inversion_termination_app₁ {t₁ t₂} :
  (app t₁ t₂)⇓ → t₁⇓.
Proof.
  refine (inversion_termination_evalcontext (papp₁ phole _) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_app₂ {t₁ t₂} :
  Value t₁ → (app t₁ t₂)⇓ → t₂⇓.
Proof.
  intros v.
  refine (inversion_termination_evalcontext (papp₂ _ phole) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_ite₁ {t₁ t₂ t₃} :
  (ite t₁ t₂ t₃)⇓ → t₁⇓.
Proof.
  refine (inversion_termination_evalcontext (pite₁ phole _ _) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_pair₁ {t₁ t₂} :
  (pair t₁ t₂)⇓ → t₁⇓.
Proof.
  refine (inversion_termination_evalcontext (ppair₁ phole _) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_pair₂ {t₁ t₂} :
  Value t₁ → (pair t₁ t₂)⇓ → t₂⇓.
Proof.
  intros v₁.
  refine (inversion_termination_evalcontext (ppair₂ _ phole) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_proj₁ {t} :
  (proj₁ t)⇓ → t⇓.
Proof.
  refine (inversion_termination_evalcontext (pproj₁ phole) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_proj₂ {t} :
  (proj₂ t)⇓ → t⇓.
Proof.
  refine (inversion_termination_evalcontext (pproj₂ phole) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_inl {t} :
  (inl t)⇓ → t⇓.
Proof.
  refine (inversion_termination_evalcontext (pinl phole) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_inr {t} :
  (inr t)⇓ → t⇓.
Proof.
  refine (inversion_termination_evalcontext (pinr phole) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_caseof₁ {t₁ t₂ t₃} :
  (caseof t₁ t₂ t₃)⇓ → t₁⇓.
Proof.
  refine (inversion_termination_evalcontext (pcaseof₁ phole _ _) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_seq₁ {t₁ t₂} :
  (seq t₁ t₂)⇓ → t₁⇓.
Proof.
  refine (inversion_termination_evalcontext (pseq₁ phole _) _ _).
  simpl; eauto.
Qed.

Lemma inversion_termination_fixt {τ₁ τ₂ t} : 
  (fixt τ₁ τ₂ t)⇓ → t⇓. 
Proof. 
  refine (inversion_termination_evalcontext (pfixt _ _ phole) _ _).
  simpl; eauto.
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

Lemma values_are_normal {t : Tm} : Value t -> normal t.
Proof.
  intros  vt.
  induction t; simpl in vt; try match goal with [ H : False |- _ ] => destruct H end; try eauto; intro et'; destruct et' as [t' et'];
  depind et'; induction C; crushStlc;
  repeat try match goal with 
      | [ H : abs _ _ -->₀ _ |- _] => depind H
      | [ H : unit -->₀ _ |- _] => depind H
      | [ H : true -->₀ _ |- _] => depind H
      | [ H : false -->₀ _ |- _] => depind H
      | [ H : pair _ _ -->₀ _ |- _] => depind H
      | [ H : inl _ -->₀ _ |- _] => depind H
      | [ H : inr _ -->₀ _ |- _] => depind H
      | [ H : pair _ _ = pair _ _ |- _] => inversion H; clear H; subst
      | [ H : inl _ = inl _ |- _] => inversion H; clear H; subst
      | [ H : inr _ = inr _ |- _] => inversion H; clear H; subst
      | [ H : _ ∧ _ |- _] => destruct_conjs
  end.
  - apply IHt1; [assumption| exists (pctx_app t' C); eauto with eval].
  - apply IHt2; [assumption| exists (pctx_app t' C); eauto with eval].
  - apply IHt; [assumption| exists (pctx_app t' C); eauto with eval].
  - apply IHt; [assumption| exists (pctx_app t' C); eauto with eval].
Qed.

Lemma TerminatingDN (t: Tm) n (m: t ⇓_ (S n)) :
  ∀ t', t --> t' → TerminatingN t' n.
Proof. 
  depind m; intros t' e'; eauto using values_are_normal.
  exfalso.
  refine (values_are_normal H _); exists t'; auto.
Qed.


Lemma TerminatingN_Terminating {t : Tm} {n} : t ⇓_ n -> t ⇓.
Proof.
  induction 1; constructor; try assumption.
  intros t' e'. exfalso. refine (values_are_normal H _).
  exists t'. auto.
Qed.
