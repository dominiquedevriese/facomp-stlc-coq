Require Export Db.Lemmas.
Require Export Stlc.SpecSyntax.
Require Export Stlc.SpecEvaluation.
Require Export Coq.Program.Tactics.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     subst*);
  try discriminate;
  eauto with eval.

(* ** Evaluation contexts *)
Lemma ectx_cat (C₁ C₂: PCtx) :
  ECtx C₁ → ECtx C₂ → ECtx (pctx_cat C₁ C₂).
Proof.
  induction C₂; simpl; intros; destruct_conjs; auto.
Qed.

Lemma pctx_cat_app (t : Tm) (C₁ C₂ : PCtx) :
  pctx_app t (pctx_cat C₁ C₂) = pctx_app (pctx_app t C₁) C₂.
Proof.
  induction C₂; crush.
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

Lemma inversion_termination_evalcontext C t (ec: ECtx C) :
  Terminating (pctx_app t C) → Terminating t.
Proof.
  intro term; depind term.
  constructor.
  eauto using eval_ctx.
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

Definition normal' (t : Tm) := ∀ t', ¬ (t --> t').
Lemma values_are_normal' {t : Tm} : Value t -> normal' t.
Proof. induction 2 using eval_ind'; crush. Qed.

Lemma values_are_normal {t : Tm} : Value t -> normal t.
Proof.
  generalize @values_are_normal'.
  unfold normal, normal', not.
  intros ? ? (); eauto.
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
