Require Stlc.SpecSyntax.
Require Stlc.SpecEvaluation.
Require Stlc.SpecTyping.
Require Stlc.LemmasTyping.
Require Import Utlc.SpecSyntax.
Require Import Utlc.SpecEvaluation.
Require Import Utlc.LemmasScoping.
Require Import LogRel.PseudoType.
Require Import LogRel.LR.
Require Import Erase.

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
  
Lemma protect_confine_closed {τ} :
  ⟨ 0 ⊢ protect τ ⟩ ∧ 
  ⟨ 0 ⊢ confine τ ⟩.
Proof.
  induction τ; simpl; crush.
  (* weakening for well-scopedness *)
Admitted.
  
Lemma protect_confine_terminate {τ vu} :
  OfTypeUtlc (embed τ) vu →
  exists vu', U.Value vu' ∧ 
              forall Cu, U.ECtx Cu → 
                         (U.pctx_app (U.app (protect τ) vu) Cu) -->* (U.pctx_app vu' Cu).
Proof.
  revert vu.
  induction τ; crush.
  - (* ptarr τ₁ τ₂ *)
    exists (abs (app (protect τ2) (app vu (app (confine τ1) (var 0))))).
    crush. 
    enough (U.pctx_app
              (U.app
                 (abs (abs (app (protect τ2) (app (var 1) (app (confine τ1) (var 0))))))
                 vu) Cu -->
              U.pctx_app (abs (app (protect τ2) (app vu (app (confine τ1) (var 0))))) Cu) by eauto with eval.
    refine (U.eval_ctx₀ _ _ _); crush.
    replace (abs (app (protect τ2) (app vu (app (confine τ1) (var 0))))) with ((abs (app (protect τ2) (app (var 1) (app (confine τ1) (var 0))))) [beta1 vu]).
    + refine (U.eval_beta _); crush.
    + simpl. repeat f_equal.
      (* Problem: no assumption currently that OfType values are closed *) 
      (* Problem: closedness implies that substitution has no effect: lemma missing? *) 
Admitted.