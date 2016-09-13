Require Import UVal.UVal.
Require Import Stlc.SpecSyntax.
Require Import Stlc.Inst.
Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.CanForm.
Require Import Db.Lemmas.
Require Import Db.WellScoping.
Require Import LogRel.LR.
Require Import LogRel.PseudoType.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     split;
     subst*);
  try discriminate;
  eauto with eval;
  repeat crushStlcSyntaxMatchH (* remove apTm's again *).

Fixpoint downgrade (n : nat) (d : nat) :=
  abs (UVal (n + d))
      (match n with
         | 0 => unkUVal 0
         | S n => 
           caseUVal (n + d) (var 0)
                    (unkUVal (S n))
                    (inUnit n (var 0))
                    (inBool n (var 0))
                    (inProd n 
                            (pair
                               (app (downgrade n d) (proj₁ (var 0)))
                               (app (downgrade n d) (proj₂ (var 0)))))
                    (inSum n 
                           (caseof (var 0)
                                   (inl (app (downgrade n d) (var 0)))
                                   (inr (app (downgrade n d) (var 0)))))
                    (inArr n
                           (abs (UVal n) 
                                (app (downgrade n d) 
                                     (app (var 1) 
                                          (app (upgrade n d) (var 0))))))
       end)
with 
upgrade (n : nat) (d : nat) :=
  abs (UVal n)
      (match n with
         | 0 => unkUVal d
         | S n => 
           caseUVal n (var 0)
                    (unkUVal (S n + d))
                    (inUnit (n + d) (var 0))
                    (inBool (n + d) (var 0))
                    (inProd (n + d) 
                            (pair
                               (app (upgrade n d) (proj₁ (var 0)))
                               (app (upgrade n d) (proj₂ (var 0)))))
                    (inSum (n + d) 
                           (caseof (var 0)
                                   (inl (app (upgrade n d) (var 0)))
                                   (inr (app (upgrade n d) (var 0)))))
                    (inArr (n + d)
                           (abs (UVal (n + d)) 
                                (app (upgrade n d) 
                                     (app (var 1) 
                                          (app (downgrade n d) (var 0))))))
       end).

Lemma upgrade_T {Γ n d} :
  ⟪ Γ ⊢ upgrade n d : UVal n ⇒ UVal (n + d) ⟫
with 
downgrade_T {Γ n d} :
  ⟪ Γ ⊢ downgrade n d : UVal (n + d) ⇒ UVal n ⟫.
Proof.
  (* can I combine eauto and crushTyping somehow? *)
  - induction n; unfold upgrade, downgrade;
    auto with typing uval_typing.
  - induction n; unfold upgrade, downgrade;
    auto with typing uval_typing.
Qed.
 
Lemma upgrade_closed {n d} :
  ⟨ 0 ⊢ upgrade n d ⟩.
Proof.
  enough (⟪ empty ⊢ upgrade n d : UVal n ⇒ UVal (n + d) ⟫) as ty by eapply (wt_implies_ws ty).
  eapply upgrade_T.
Qed.

Lemma downgrade_closed {n d} :
  ⟨ 0 ⊢ downgrade n d ⟩.
Proof.
  enough (⟪ empty ⊢ downgrade n d : UVal (n + d) ⇒ UVal n ⟫) as ty by eapply (wt_implies_ws ty).
  eapply downgrade_T.
Qed.

Lemma upgrade_sub {n d γ} : (upgrade n d)[γ] = upgrade n d.
Proof.
  (* Sigh why is coq not finding this instance??? *) 
(*   About wsApTm. *)
(*   apply wsClosed_invariant.  *)
(*   eapply upgrade_closed. *)
(* Qed. *)
Admitted.

Lemma downgrade_sub {n d γ} : (downgrade n d)[γ] = downgrade n d.
Proof.
Admitted.


Lemma downgrade_value {n d} : Value (downgrade n d).
Proof.
  destruct n; simpl; trivial.
Qed.

Lemma upgrade_value {n d} : Value (downgrade n d).
Proof.
  destruct n; simpl; trivial.
Qed.

Lemma downgrade_zero_eval {d v} : Value v → app (downgrade 0 d) v -->* unkUVal 0.
Proof.
  intros vv.
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  simpl; eauto with eval. 
Qed.

Lemma downgrade_eval_unk {n d} : app (downgrade n d) (unkUVal (n + d)) -->* unkUVal n.
Proof.
  assert (vv : Value (unkUVal (n + d))) by apply unkUVal_Value.
  destruct n; simpl.
  - eapply evalStepStar. eapply eval₀_to_eval. crush.
    simpl; eauto with eval. 
  - change _ with (Value (inl unit)) in vv.
    eapply evalStepStar. eapply eval₀_to_eval. crush.
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
    eapply caseUVal_eval_unk.
Qed.

Lemma downgrade_eval_inUnit {n d v} : 
  Value v → app (downgrade (S n) d) (inUnit (n + d) v) -->* inUnit n v.
Proof.
  intros vv.
  assert (Value (inUnit (n + d) v)) by (simpl; crush).
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
  eapply evalStepTrans. eapply caseUVal_eval_unit; crush.
  simpl; crush.
Qed.
  
Lemma downgrade_eval_inBool {n d v} : 
  Value v → app (downgrade (S n) d) (inBool (n + d) v) -->* inBool n v.
Proof.
  intros vv.
  assert (Value (inBool (n + d) v)) by (simpl; crush).
  unfold downgrade.
  eapply evalStepStar. eapply eval₀_to_eval. crush.
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
  eapply evalStepTrans. eapply caseUVal_eval_bool; crush.
  simpl; crush.
Qed.
 
Lemma downgrade_eval_inProd {n d v₁ v₂ v₁' v₂'} : 
  Value v₁ → Value v₂ → Value v₁' → Value v₂' →
  app (downgrade n d) v₁ -->* v₁' →
  app (downgrade n d) v₂ -->* v₂' →
  app (downgrade (S n) d) (inProd (n + d) (pair v₁ v₂)) -->* inProd n (pair v₁' v₂').
Proof.
  intros vv₁ vv₂ vv₁' vv₂' es₁ es₂.
  assert (Value (inProd (n + d) (pair v₁ v₂))) by (simpl; crush).
  unfold downgrade.
  assert (Value (downgrade n d)) by apply downgrade_value.

  (* beta-reduce *)
  eapply evalStepStar. eapply eval₀_to_eval; crush.
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush.
  rewrite -> ?upgrade_sub, ?downgrade_sub.

  (* evaluate UVal pattern match *)
  eapply evalStepTrans. eapply caseUVal_eval_prod; crush.
  (* downgrade under sub... *)
  simpl; crush.
  rewrite -> ?downgrade_sub.

  (* first projection *)
  eapply evalStepStar. 
  assert (ep₁ : proj₁ (pair v₁ v₂) -->₀ v₁) by crush.
  eapply (eval_from_eval₀ ep₁); inferContext; crush; simpl.

  (* recursive call 1 *)
  eapply evalStepTrans. eapply (evalstar_ctx' es₁); inferContext; crush.

  (* second projection *)
  eapply evalStepStar. 
  assert (ep₂ : proj₂ (pair v₁ v₂) -->₀ v₂) by crush.
  eapply (eval_from_eval₀ ep₂); inferContext; crush; simpl.

  (* recursive call 2 *)
  eapply evalStepTrans. eapply (evalstar_ctx' es₂); inferContext; crush.

  (* ... and we're done. *)
  simpl; crush.
Qed.

Lemma downgrade_eval_inSum {n d v v' va va'} : 
  Value v → Value v' → 
  (va = inl v ∧ va' = inl v') ∨ (va = inr v ∧ va' = inr v') →
  app (downgrade n d) v -->* v' →
  app (downgrade (S n) d) (inSum (n + d) va) -->* inSum n va'.
Proof.
  intros vv vv' eqs es.

  unfold downgrade.
  destruct eqs as [(? & ?)|(? & ?)]; subst;
  (* beta-reduce *)
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
    rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
    rewrite -> ?upgrade_sub, ?downgrade_sub;

    (* evaluate UVal pattern match *)
    (eapply evalStepTrans; [eapply caseUVal_eval_sum; crush|]);
    (* downgrade under sub... *)
    simpl; crush;
    rewrite -> ?downgrade_sub;

    (* caseof *)
    [assert (ec : caseof (inl v) (inl (app (downgrade n d) (var 0))) (inr (app (downgrade n d) (var 0))) -->₀ ((inl (app (downgrade n d) (var 0))) [beta1 v])) by crush
    |assert (ec : caseof (inr v) (inl (app (downgrade n d) (var 0))) (inr (app (downgrade n d) (var 0))) -->₀ ((inr (app (downgrade n d) (var 0))) [beta1 v])) by crush
    ];
    (eapply evalStepStar;
     [eapply (eval_from_eval₀ ec); inferContext; crush|]);
    crushStlcSyntaxMatchH (* why is this needed? *);
    rewrite -> ?downgrade_sub;

    (* recursive call *)
    (eapply evalStepTrans; [eapply (evalstar_ctx' es); inferContext; crush|]);

    (* ... and we're done. *)
    simpl; crush.
Qed.

Lemma downgrade_eval_inArr {n d v} : 
  Value v →
  app (downgrade (S n) d) (inArr (n + d) v) -->* 
      inArr n (abs (UVal n) (app (downgrade n d) (app (v[wk]) (app (upgrade n d) (var 0))))).
Proof.
  intros vv.
  unfold downgrade.

  (* beta-reduce *)
  (eapply evalStepStar; [eapply eval₀_to_eval; crush|]);
  rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush;
  rewrite -> ?upgrade_sub, ?downgrade_sub.

  (* evaluate UVal pattern match *)
  (eapply evalStepTrans; [eapply caseUVal_eval_arr; crush|]);
    (* downgrade under sub... *)
    simpl; crush;
    rewrite -> ?downgrade_sub, ?upgrade_sub.

  change (wk 0) with 1; simpl.
  eauto with eval.
Qed.

Lemma downgrade_reduces {n d v} :
  ⟪ empty ⊢ v : UVal (n + d) ⟫ → Value v →
  exists v', Value v' ∧ app (downgrade n d) v -->* v'.
             (* ∧ (forall vu dir w p, valrel dir w (pEmulDV (n + d) p) v vu → valrel dir w (pEmulDV n p) v' vu). *)
Proof.
  revert v; induction n;
  intros v ty vv.
  - exists (unkUVal 0).
    eauto using unkUVal_Value, downgrade_zero_eval.
  - canonUVal. 
    + exists (unkUVal (S n)).
      change (S (n + d)) with (S n + d).
      eauto using unkUVal_Value, downgrade_eval_unk.
    + exists (inUnit n x).
      eauto using inUnit_Value, downgrade_eval_inUnit.
    + exists (inBool n x).
      eauto using inBool_Value, downgrade_eval_inBool.
    + stlcCanForm.
      destruct H0 as (vx0 & vx1).
      destruct (IHn _ H2 vx0) as (x0' & vx0' & evalx0).
      destruct (IHn _ H3 vx1) as (x1' & vx1' & evalx1).
      exists (inProd n (pair x0' x1')).
      assert (Value (pair x0' x1')) by crush.
      eauto using inProd_Value, downgrade_eval_inProd.

    + stlcCanForm;
      [ destruct (IHn _ H2 H0) as (vf & vvf & ex);
        exists (inSum n (inl vf))
      | destruct (IHn _ H2 H0) as (vf & vvf & ex);
        exists (inSum n (inr vf))];
      eauto using inSum_Value, downgrade_eval_inSum.
    + exists (inArr n (abs (UVal n) (app (downgrade n d) (app (x[wk]) (app (upgrade n d) (var 0)))))).
      assert (Value (abs (UVal n) (app (downgrade n d) (app (x[wk]) (app (upgrade n d) (var 0)))))) by crush.
      eauto using inArr_Value, downgrade_eval_inArr.
Qed.
  