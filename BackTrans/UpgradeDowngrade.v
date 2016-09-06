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

Lemma downgrade_reduces {n d v} :
  ⟪ empty ⊢ v : UVal (n + d) ⟫ → Value v →
  exists v', Value v' ∧ app (downgrade n d) v -->* v'.
Proof.
  revert v; induction n;
  intros v ty vv; simpl.
  - exists (unkUVal 0); crush.
    eapply evalStepStar. eapply eval₀_to_eval. crush.
    simpl; eauto with eval. 
  - destruct (canonUVal ty vv) as 
        [?|[(v' & eq & vv' & tyv')|
            [(v' & eq & vv' & tyv')|
             [(v' & eq & vv' & tyv')|
              [(v' & eq & vv' & tyv')|
               (v' & eq & vv' & tyv')]]]]]; subst.
    + exists (unkUVal (S n)); crush.
      assert (Value (unkUVal 0)) by crush.
      eapply evalStepStar. eapply eval₀_to_eval; crush.
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
      eapply caseUVal_eval_unk.
    + exists (inUnit n v'); crush.
      eapply evalStepStar. eapply eval₀_to_eval; crush.
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
      eapply evalStepTrans. eapply caseUVal_eval_unit; crush.
      simpl; crush.
    + exists (inBool n v'); crush.
      eapply evalStepStar. eapply eval₀_to_eval; crush.
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
      eapply evalStepTrans. eapply caseUVal_eval_bool; crush.
      simpl; crush.
    + stlcCanForm.
      destruct vv' as (vx & vx0).
      destruct (IHn x H0 vx) as (x' & vx' & evalx).
      destruct (IHn x0 H1 vx0) as (x0' & vx0' & evalx0).
      exists (inProd n (pair x' x0')); crush.

      assert (Value (pair x x0)) by crush.
      assert (Value (downgrade n d)) by (apply downgrade_value).

      (* beta-reduce *)
      eapply evalStepStar. eapply eval₀_to_eval; crush.
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl; crush.
      rewrite -> ?upgrade_sub, ?downgrade_sub.

      (* evaluate UVal pattern match *)
      eapply evalStepTrans. eapply caseUVal_eval_prod; crush.
      (* downgrade under sub... *)
      simpl; crush.
      rewrite -> ?upgrade_sub, ?downgrade_sub.

      (* first projection *)
      eapply evalStepStar. 
      assert (ep₁ : proj₁ (pair x x0) -->₀ x) by crush.
      eapply (eval_from_eval₀ ep₁); inferContext; crush; simpl.

      (* recursive call 1 *)
      eapply evalStepTrans. eapply (evalstar_ctx' evalx); inferContext; crush.

      (* second projection *)
      eapply evalStepStar. 
      assert (ep₂ : proj₂ (pair x x0) -->₀ x0) by crush.
      eapply (eval_from_eval₀ ep₂); inferContext; crush; simpl.

      (* recursive call 2 *)
      eapply evalStepTrans. eapply (evalstar_ctx' evalx0); inferContext; crush.

      (* ... and we're done. *)
      simpl; crush.

    + admit.
    + admit.
Admitted.
  