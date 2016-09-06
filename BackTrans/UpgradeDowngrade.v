Require Import UVal.UVal.
Require Import Stlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.CanForm.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     split;
     subst*);
  try discriminate;
  eauto with eval.

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
  intros v ty vv; unfold downgrade.
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
      exists (pair x' x0'); crush.
      assert (Value (pair x x0)) by crush.
      eapply evalStepStar. eapply eval₀_to_eval; crush.
      rewrite -> ?(caseUVal_sub (beta1 _)); simpl.
      eapply evalStepTrans. eapply caseUVal_eval_prod; crush.
      (* downgrade under sub... *)
      eapply evalStepTrans. eapply (evalstar_ctx' evalx); inferContext.
      simpl; crush.
      
    + admit.
    + admit.
Admitted.
  