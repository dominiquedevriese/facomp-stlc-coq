Require Export Db.Lemmas.
Require Export Stlc.SpecSyntax.
Require Export Stlc.SpecEvaluation.
Require Export Coq.Program.Tactics.
Require Import Common.Common.
Require Import Common.Relations.

Require Import Omega.

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
  induction 1; eauto using eval_ctx with eval.
Qed.

Lemma evalplus_ctx C t t' (eC: ECtx C) :
  t -->+ t' → pctx_app t C -->+ pctx_app t' C.
Proof. 
  induction 1; eauto using eval_ctx with eval.
Qed.

Lemma evaln_ctx {C t t' n} :
  ECtx C → evaln t t' n -> evaln (pctx_app t C) (pctx_app t' C) n.
Proof.
  intros ec.
  induction 1; unfold evaln; eauto using eval_ctx with eval.
Qed.

Lemma termination_closed_under_antireduction {t t'} :
  t --> t' → t'⇓ → t⇓.
Proof.
  destruct 2 as [v ?].
  exists v; crush.
Qed.


Lemma terminationN_closed_under_antireduction {t t' n} :
  t --> t' → TerminatingN t' n → TerminatingN t (S n).
Proof.
  destruct 2 as (v & m & ? & ? & ?).
  exists v, (S m); repeat split.
  - crush.
  - omega.
  - eapply stepRel_step; crush.
Qed.


Lemma termination_closed_under_antireductionStar {t t'} :
  t -->* t' → t'⇓ → t⇓.
Proof.
  intros e m. induction e; 
  eauto using termination_closed_under_antireduction.
Qed.

Lemma eval_ectx_inv C t (ec : ECtx C) t' :
  pctx_app t C --> t' →
  Value t ∨ exists t'', t' = pctx_app t'' C ∧ t --> t''.
Admitted.

Lemma value_ectx_inv C t (ec : ECtx C) :
  Value (pctx_app t C) → Value t.
Proof.
  intros v; induction C; crush.
Qed.

Lemma evalStar_ectx_inv C t (ec : ECtx C) v :
  pctx_app t C -->* v → Value v →
  exists v', Value v' ∧ t -->* v' ∧ pctx_app v' C -->* v.
Proof.
  intros es vv; depind es.
  - exists t; eauto using value_ectx_inv with eval.
  - destruct (eval_ectx_inv C t ec _ H) as [vt|[t'' [eq e]]].
    + exists t; crush.
    + subst.
      destruct (IHes t'' C ec eq_refl vv) as (v' & vv' & es1' & es2').
      exists v'; crush.
Qed.
         
Lemma values_terminate {v : Tm} : Value v → v ⇓.
Proof.
  intros vv. exists v; crush.
Qed.

Lemma inversion_termination_evalcontext C t (ec: ECtx C) :
  Terminating (pctx_app t C) → Terminating t.
Proof.
  destruct 1 as (v & vv & es).
  destruct (evalStar_ectx_inv C t ec v es) as (v' & vv' & es1 & es2); subst; crush.
  exists v'; crush.
Qed.

Corollary divergence_closed_under_evalcontex t :
  t⇑ → ∀ p, ECtx p → (pctx_app t p)⇑.
Proof. eauto using inversion_termination_evalcontext. Qed.

Definition normal' (t : Tm) := ∀ t', ¬ (t --> t').
Lemma values_are_normal' {t : Tm} : Value t -> normal' t.
Proof. induction 2 using eval_ind'; crush. Qed.

Lemma values_are_normal {t : Tm} : Value t -> normal t.
Proof.
  generalize @values_are_normal'.
  unfold normal, normal', not.
  intros ? ? (); eauto.
Qed.

Lemma values_terminateN {t n} : Value t → t ⇓_ n.
Proof.
  intros v. exists t, 0; repeat split.
  - crush.
  - omega.
  - eapply stepRel_zero.
Qed.

Ltac crushImpossibleEvals :=
  match goal with
          [ H : abs _ _ --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : true --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : false --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : unit --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H); crush
        | [ H : Value ?x, H' : ?x --> _ |- _ ] => exfalso; refine (values_are_normal' H _ H'); crush
        | [ Hx : Value ?x, Hy : Value ?y,  H' : pair ?x ?y --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
        | [ Hx : Value ?x,  H' : inl ?x --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
        | [ Hx : Value ?x,  H' : inr ?x --> _ |- _ ] => exfalso; refine (values_are_normal' _ _ H'); crush
  end.

Lemma evaln_to_evalStar {t t' n} : evaln t t' n → t -->* t'.
Proof.
  induction 1; crush.
Qed.

Lemma TerminatingN_Terminating {t : Tm} {n} : t ⇓_ n -> t ⇓.
Proof.
  destruct 1 as (v & m & vv & ineq & es).
  exists v; eauto using evaln_to_evalStar.
Qed.

Lemma evalStar_to_evaln {t t'} : t -->* t' → exists n, evaln t t' n.
Proof.
  induction 1.
  - exists 0; apply stepRel_zero.
  - destruct (IHclos_refl_trans_1n) as (n & en).
    exists (S n); eapply stepRel_step; crush.
Qed.

(* This should hold, but doesn't? *)
Lemma Terminating_TerminatingN {t : Tm} : t ⇓ -> ∃ n, t ⇓_ n.
Proof.
  destruct 1 as (v & vv & es).
  destruct (evalStar_to_evaln es) as [n en].
  exists n; econstructor; crush.
Qed.

Lemma determinacy' {t t' t'' t'''} : t --> t' → t'' --> t''' → t = t'' → t' = t'''.
Proof.
  intros e₁.
  revert t'' t'''.
  induction e₁ using eval_ind';
  induction 1 using eval_ind'; crush; try crushImpossibleEvals.
Qed.

Lemma determinacy {t t' t''} : t --> t' → t --> t'' → t' = t''.
Proof.
  eauto using determinacy'.
Qed.

Lemma TerminatingD (t: Tm) (m: t⇓) :
  ∀ t', t --> t' → Terminating t'.
Proof. 
  destruct m as (v & vv & es). 
  destruct es; 
  intros t' e; try crushImpossibleEvals.
  destruct (determinacy H e).
  exists z; crush.
Qed.

Lemma TerminatingDN (t: Tm) n (term: t ⇓_ (S n)) :
  ∀ t', t --> t' → TerminatingN t' n.
Proof. 
  destruct term as (v & m & vv & ineq & esn). 
  intros t' e.
  destruct esn; try crushImpossibleEvals.
  destruct (determinacy H e).
  exists t'', n0; repeat split.
  - crush.
  - omega.
  - crush.
Qed.

Lemma termination_closed_under_evalplus {t t'} :
  t -->+ t' → t⇓ → t'⇓.
Proof. intros e m; induction e; eauto using TerminatingD. Qed.

Lemma termination_closed_under_evalstar {t t'} :
  t -->* t' → t⇓ → t'⇓.
Proof. intros e m; induction e; eauto using TerminatingD. Qed.

Corollary divergence_closed_under_eval {t t'} :
  t --> t' → t'⇑ → t⇑.
Proof. eauto using TerminatingD with eval. Qed.

Corollary divergence_closed_under_evalplus {t t'} :
  t -->+ t' → t'⇑ → t⇑.
Proof. eauto using termination_closed_under_evalplus. Qed.

Corollary divergence_closed_under_evalstar {t t'} :
  t -->* t' → t'⇑ → t⇑.
Proof. eauto using termination_closed_under_evalstar. Qed.

Lemma cycles_dont_terminate {t} :
  t -->+ t → t⇑.
Admitted.

Lemma TerminatingN_lt {t n n'} :
  TerminatingN t n → n ≤ n' → TerminatingN t n'.
Proof.
  destruct 1 as (v & m & vv & ineq & esm).
  intros ineq'.
  exists v, m; repeat split; crush.
  omega.
Qed.

(* Lemma TerminatingN_eval1 {t t' n} : *)
(*   t --> t' → TerminatingN t' n → TerminatingN t (S n). *)
(* Proof. *)
(*   intros e term. *)
(*   destruct term as [v m]. *)
(*   apply (TerminatingIN t (S n) v (S m)); crush; try omega. *)
(*   eapply stepRel_step; crush. *)
(* Qed. *)

Lemma TerminatingN_eval {t t' n} :
  t --> t' → TerminatingN t' n ↔ TerminatingN t (S n).
Proof.
  intros term.
  split; intros; 
  [eapply terminationN_closed_under_antireduction | eapply TerminatingDN];
  crush.
Qed.
    
Lemma TerminatingN_evaln {t t' n } n' :
  evaln t t' n → TerminatingN t' n' ↔ TerminatingN t (n + n').
Proof.
  induction 1; constructor; auto; intro term;
  change (S n + n') with (S (n + n')) in *;
  [rewrite <- (TerminatingN_eval H) | rewrite <- (TerminatingN_eval H) in term];
  apply IHstepRel; auto.
Qed.

Lemma evaln_split {t t' } n n':
  evaln t t' (n + n') → exists t'', evaln t t'' n ∧ evaln t'' t' n'.
Proof.
  revert t; induction n.
  - intros; exists t; simpl in *; split; [apply stepRel_zero|assumption].
  - intros t esn; depind esn; clear IHesn.
    destruct (IHn t' esn) as (t3 & es1 & es2).
    exists t3; split; try assumption.
    eapply stepRel_step; crush.
Qed.


Lemma TerminatingN_xor_evaln {t t' n} :
  TerminatingN t n → evaln t t' (S n) → False.
Proof.
  intros term esn.
  replace (S n) with (n + 1) in esn by omega.
  destruct (evaln_split n 1 esn) as (t'' & en & e1).
  replace n with (n + 0) in term by omega.
  rewrite <- (TerminatingN_evaln 0 en) in term.
  destruct term as (v & m & vv & ineq & esm).
  assert (m = 0) by omega; subst.
  inversion esm; subst.
  inversion e1.
  crushImpossibleEvals.
Qed.

Section EvalInContext.
  Lemma eval₀_to_eval {t t'} :
    t -->₀ t' →
    t --> t'.
  Proof.
    intros e₀.
    change (t --> t') with (pctx_app t phole --> pctx_app t' phole).  
    eapply (eval_ctx₀ phole); crush.
  Qed.

  Lemma eval_from_eval₀ {t t' t₀ t₀' C} :
    t₀ -->₀ t₀' →
    t = pctx_app t₀ C →
    t' = pctx_app t₀' C →
    ECtx C →
    t --> t'.
  Proof.
    intros; subst; eauto using eval_ctx₀.
  Qed.

  Lemma evalstar_ctx' {t t' t₀ t₀' C} :
    t₀ -->* t₀' →
    t = pctx_app t₀ C →
    t' = pctx_app t₀' C →
    ECtx C →
    t -->* t'.
  Proof.
    intros; subst; eauto using evalstar_ctx.
  Qed.

End EvalInContext.

Ltac inferContext :=
  simpl; try reflexivity;
  let rec inferC acc t t₀ :=
      match t with
        | t₀ => instantiate (1 := acc)
        | app ?t1 ?t2 => inferC (pctx_cat (papp₁ phole t2) acc) t1 t₀ + inferC (pctx_cat (papp₂ t1 phole) acc) t2 t₀
        | pair ?t1 ?t2 => inferC (pctx_cat (ppair₁ phole t2) acc) t1 t₀ + inferC (pctx_cat (ppair₂ t1 phole) acc) t2 t₀
        | seq ?t1 ?t2 => inferC (pctx_cat (pseq₁ phole t2) acc) t1 t₀
        | inl ?t1 => inferC (pctx_cat (pinl phole) acc) t1 t₀
        | inr ?t1 => inferC (pctx_cat (pinl phole) acc) t1 t₀
        | inr ?t1 => inferC (pctx_cat (pinl phole) acc) t1 t₀
        | ite ?t1 ?t2 ?t3 => inferC (pctx_cat (pite₁ phole t2 t3) acc) t1 t₀
        | caseof ?t1 ?t2 ?t3 => inferC (pctx_cat (pcaseof₁ phole t2 t3) acc) t1 t₀
        | proj₁ ?t1 => inferC (pctx_cat (pproj₁ phole) acc) t1 t₀
        | proj₂ ?t1 => inferC (pctx_cat (pproj₂ phole) acc) t1 t₀
        | pctx_app ?t1 (pctx_cat ?C1 ?C2) => inferC (pctx_app (pctx_app t1 C1) C2) t₀
        | pctx_app ?t1 ?C => inferC (pctx_cat C acc) t1 t₀
      end
  in repeat match goal with
              | [ |- ?t = pctx_app ?t₀ (pctx_cat ?C1 ?C2) ] => (rewrite -> ?pctx_cat_app)
              | [ |- pctx_app ?t0 ?C = pctx_app ?t' ?C ] => f_equal
              | [ |- ?t = pctx_app ?t₀ ?C ] => (inferC phole t t₀; rewrite -> ?pctx_cat_app; simpl; rewrite -> ?pctx_cat_app in *; reflexivity)
            end.
  
Lemma test_inferContext (t : Tm) (C' : PCtx): True.
Proof.
  assert (pctx_app (pair (inl t) unit) C' = pctx_app t (pctx_cat (ppair₁ (pinl phole) unit) C')).
  inferContext.
  trivial.
Qed.