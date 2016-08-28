Require Stlc.SpecSyntax.
Require Stlc.SpecEvaluation.
Require Stlc.SpecTyping.
Require Stlc.LemmasTyping.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.LemmasScoping.
Require Import Utlc.Inst.
Require Import Utlc.DecideEval.
Require Import LogRel.PseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import Erase.

Module S.
     Include Stlc.SpecSyntax.
     Include Stlc.SpecEvaluation.
     Include Stlc.SpecTyping.
     Include Stlc.LemmasTyping.
End S.

Module U.
  Include Utlc.SpecSyntax.
  Include Utlc.SpecEvaluation.
End U.

Fixpoint protect (ty : S.Ty) : U.UTm :=
  abs (match ty with
         | S.tunit => var 0
         | S.tbool => var 0
         | S.tarr ty1 ty2 => abs (app (protect ty2) (app (var 1) (app (confine ty1) (var 0))))
         | S.tprod ty1 ty2 => pair (app (protect ty1) (proj₁ (var 0))) (app (protect ty2) (proj₂ (var 0)))
         | S.tsum ty1 ty2 => caseof (var 0) (inl (app (protect ty1) (var 0))) (inr (app (protect ty2) (var 0)))
       end)
with confine (ty : S.Ty) : U.UTm :=
  abs (match ty with
         | S.tunit => seq (var 0) unit
         | S.tbool => ite (var 0) true false
         | S.tarr ty1 ty2 => abs (app (confine ty2) (app (var 1) (app (protect ty1) (var 0))))
         | S.tprod ty1 ty2 => pair (app (confine ty1) (proj₁ (var 0))) (app (confine ty2) (proj₂ (var 0)))
         | S.tsum ty1 ty2 => caseof (var 0) (inl (app (confine ty1) (var 0))) (inr (app (confine ty2) (var 0)))
       end).


Local Ltac crush :=
  repeat (try intros;
          simpl;
          intuition; 
          repeat crushOfTypeUtlcMatch;
          repeat crushUtlcScoping;
          repeat crushUtlcSyntaxMatchH;
          repeat crushUtlcEvaluationMatchH;
          repeat match goal with
                     [ |- _ ∧ _ ] => split
                   | [ |- OfType _ _ _ ] => unfold OfType, OfTypeStlc
                   | [ H: OfType _ _ _  |- _ ] => destruct H as [[? ?] ?]
                   | [ H: OfTypeStlc _ _  |- _ ] => destruct H as [? ?]
                 end;
          S.crushTyping
         ).
  
Lemma protect_confine_closed τ :
  ⟨ 0 ⊢ protect τ ⟩ ∧ 
  ⟨ 0 ⊢ confine τ ⟩.
Proof.
  induction τ; simpl; crush;
  try match goal with
      [ H : ⟨ 0 ⊢ ?t ⟩ |- ⟨ ?d ⊢ ?t ⟩ ] => (rewrite <- (wsClosed_invariant H (wkms d));
                                            exact (weakenings d H))
  end.
Qed.
  
Lemma protect_confine_terminate {τ vu} :
  OfTypeUtlc (embed τ) vu →
  exists vu', U.Value vu' ∧ 
              forall Cu, U.ECtx Cu → 
                         (U.pctx_app (U.app (protect τ) vu) Cu) -->* (U.pctx_app vu' Cu).
Proof.
  revert vu.
  induction τ; crush.
  - (* ptarr τ₁ τ₂ *)
    exists (abs (app (protect τ2) (app vu[wkm] (app (confine τ1) (var 0))))).
    crush. 
    enough (U.pctx_app
              (U.app
                 (abs (abs (app (protect τ2) (app (var 1) (app (confine τ1) (var 0))))))
                 vu) Cu -->
              U.pctx_app (abs (app (protect τ2) (app vu[wkm] (app (confine τ1) (var 0))))) Cu) by eauto with eval.
    refine (U.eval_ctx₀ _ _ _); crush.
    replace (abs (app (protect τ2) (app vu[wkm] (app (confine τ1) (var 0))))) with 
      ((abs (app (protect τ2) (app (var 1) (app (confine τ1) (var 0))))) [beta1 vu]).
    + refine (U.eval_beta _); crush.
    + pose (protect_confine_closed τ2).
      pose (protect_confine_closed τ1).
      crush; eauto using wsClosed_invariant.
      (* vu[wkm] = vu[wkm]:  applying the weakening substitution is the same as the renaming: lemma missing? *)
      admit.
  - (* ptunit *)
    exists unit; crush.
    eapply evaln_to_evalStar.
    subst; apply (evalMax 10 (app (abs (var 0)) unit) nil (idm UTm)); crush.
  - (* ptbool *)
    exists true; crush.
    eapply evaln_to_evalStar.
    subst; apply (evalMax 10 (app (abs (var 0)) true) nil (idm UTm)); crush.
  - (* ptbool *)
    exists false; crush.
    eapply evaln_to_evalStar.
    subst; apply (evalMax 10 (app (abs (var 0)) false) nil (idm UTm)); crush.
  - destruct H as [t₁ [t₂ [eq [ot1 ot2]]]]; subst.
    destruct (IHτ1 t₁ ot1) as [v1 [vv1 e1]].
    destruct (IHτ2 t₂ ot2) as [v2 [vv2 e2]].
    exists (pair v1 v2); crush.
    

    
        
      (* Problem: no assumption currently that OfType values are closed *) 
      (* Problem: closedness implies that substitution has no effect: lemma missing? *) 
Admitted.