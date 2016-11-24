Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.StlcOmega.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.DecideEval.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import Omega.
Require Import Db.Lemmas.


Require Import LogRel.LR.
Require Import Compiler.ProtectConfine.

Require Import BackTrans.UValHelpers.

Require Import UVal.UVal.

Fixpoint inject (n : nat) (τ : Ty) :=
  S.abs τ
      (match τ with
         | tarr τ₁ τ₂ => inArrDwn n (S.abs (UVal n) (S.app (inject n τ₂) (S.app (S.var 1) (S.app (extract n τ₁) (S.var 0)))))
         | tunit => inUnitDwn n (S.var 0) 
         | tbool => inBoolDwn n (S.var 0)
         | tprod τ₁ τ₂ => inProdDwn n (S.pair (S.app (inject n τ₁) (S.proj₁ (S.var 0))) 
                                         (S.app (inject n τ₂) (S.proj₂ (S.var 0))))
         | tsum τ₁ τ₂ => inSumDwn n (S.caseof (S.var 0) (S.inl (S.app (inject n τ₁) (S.var 0))) 
                                         (S.inr (S.app (inject n τ₂) (S.var 0))))
       end)
with extract (n : nat) (τ : Ty) :=
       S.abs (UVal n) (match τ with
                       | tarr τ₁ τ₂ => S.abs τ₁ (S.app (extract n τ₂) (S.app (caseArrUp n (S.var 1)) (S.app (inject n τ₁) (S.var 0))))
                       | tunit => caseUnitUp n (S.var 0)
                       | tbool => caseBoolUp n (S.var 0)
                       | tprod τ₁ τ₂ => S.pair (S.app (extract n τ₁) (S.proj₁ (caseProdUp n (S.var 0))))
                                             (S.app (extract n τ₂) (S.proj₂ (caseProdUp n (S.var 0))))
                       | tsum τ₁ τ₂ => S.caseof (caseSumUp n (S.var 0))
                                              (S.inl (S.app (extract n τ₁) (S.var 0)))
                                              (S.inr (S.app (extract n τ₂) (S.var 0)))
                     end).


Lemma injectT {n τ Γ} : ⟪ Γ ⊢ inject n τ : τ ⇒ UVal n ⟫
with extractT {n τ Γ} : ⟪ Γ ⊢ extract n τ : UVal n ⇒ τ ⟫. 
Proof.
  - induction τ; unfold inject; eauto with typing uval_typing.
  - induction τ; unfold extract; eauto with typing uval_typing.
Qed.

Lemma inject_closed {n τ} :
  ⟨ 0 ⊢ inject n τ ⟩.
Proof.
  eapply (wt_implies_ws (Γ := empty)).
  eapply injectT.
Qed.

Lemma extract_closed {n τ} :
  ⟨ 0 ⊢ extract n τ ⟩.
Proof.
  eapply (wt_implies_ws (Γ := empty)).
  eapply extractT.
Qed.

Lemma inject_sub {n τ γ} : (inject n τ)[γ] = inject n τ.
Proof.
  apply wsClosed_invariant.
  eapply inject_closed.
Qed.

Lemma extract_sub {n τ γ} : (extract n τ)[γ] = extract n τ.
Proof.
  apply wsClosed_invariant.
  eapply extract_closed.
Qed.

Lemma inject_and_protect_work {n w d p τ vs vu} :
  dir_world_prec n w d p →
  valrel d w (embed τ) vs vu →
  termrel₀ d w (pEmulDV n p) (S.app (inject n τ) vs) (U.app (protect τ) vu).
Proof.
  revert n w vs vu.
  induction τ;
  intros n w vs vu dwp vr; simpl.
  - (* τ₁ ⇒ τ₂ *) 
    destruct (valrel_implies_Value vr) as (vvs & vvu).
    eapply termrel₀_antired_star.
    + eapply evalToStar.
      eapply (S.eval_ctx₀ S.phole); simpl;
      eauto using S.eval_beta.
    + eapply evalToStar.
      eapply U.eval₀_ctxeval.
      eapply U.eval_beta; eauto.
    + cbn.
      rewrite inArrDwn_sub, protect_sub, confine_sub. 
      crushTyping.
      rewrite inject_sub, extract_sub; cbn.
      crushUtlcScoping.
      rewrite protect_sub, confine_sub.