Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Stlc.StlcOmega.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.LemmasEvaluation.
Require Import Utlc.DecideEval.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import LogRel.LemmasInversion.
Require Import Omega.
Require Import Db.Lemmas.


Require Import LogRel.LR.
Require Import Compiler.ProtectConfine.

Require Import BackTrans.UValHelpers.

Require Import UVal.UVal.

Local Ltac crush :=
  cbn in * |-;
  repeat
    (repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushRepEmulEmbed;
     repeat crushUtlcSyntaxMatchH;
     repeat crushUtlcScopingMatchH;
     repeat crushUtlcScopingMatchH;
     repeat crushUtlcEvaluationMatchH2;
     split;
     trivial;
     crushTyping;
     try crushOfType;
     subst*);
  try discriminate; try Omega.omega;
  eauto with eval;
  repeat crushStlcSyntaxMatchH; (* remove apTm's again *)
  repeat crushUtlcSyntaxMatchH. (* same for apUTm's *)

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

Lemma inject_value {n τ} : S.Value (inject n τ).
Proof.
  (* exact I. *)
  (* Should be doable without the induction, but I don't see how *)
  induction τ; simpl; eauto with eval.
Qed.

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
  termrel₀ d w (pEmulDV n p) (S.app (inject n τ) vs) (U.app (protect τ) vu)
with extract_and_confine_work {n w d p τ vs vu} :
  dir_world_prec n w d p →
  valrel d w (pEmulDV n p) vs vu →
  termrel₀ d w (embed τ) (S.app (extract n τ) vs) (U.app (confine τ) vu).
Proof.
  - revert n w vs vu.
    induction τ;
      intros n w vs vu dwp vr; 
      destruct (valrel_implies_OfType vr) as ((_ & tvs) & (closed_vu & _));
      destruct (valrel_implies_Value vr) as (vvs & vvu);
      simpl.
    + (* τ₁ ⇒ τ₂ *) 
      eapply termrel₀_antired_star.
      * eapply evalToStar.
        eapply (S.eval_ctx₀ S.phole); simpl;
        eauto using S.eval_beta.
      * eapply evalToStar.
        eapply U.eval₀_ctxeval.
        eapply U.eval_beta; eauto.
      * cbn.
        rewrite inArrDwn_sub, protect_sub, confine_sub. 
        crushTyping.
        rewrite inject_sub, extract_sub; cbn.
        crushUtlcScoping.
        rewrite ?protect_sub, ?confine_sub.

        eapply termrel₀_inArrDwn; try assumption.
        
        change (UVal n) with (repEmul (pEmulDV n p)). 
        eapply valrel_lambda. 
        { eapply OfType_lambda; auto.
          - crushUtlcScoping; eauto using protect_closed, confine_closed.
          - crushTyping; rewrite repEmul_embed_leftinv; eauto using injectT, extractT.
        } 
        { intros w' vs' vu' fw' vr'.
          cbn.
          crushUtlcScoping.
          crushTyping.
          rewrite ?protect_sub, ?confine_sub.
          rewrite ?inject_sub, ?extract_sub.
          rewrite ?(wsClosed_invariant (wt_implies_ws tvs)).
          rewrite ?(wsClosed_invariant closed_vu).

          (* execute the extract/confine *)
          assert (dir_world_prec n w' d p) as dwp' by eauto using dwp_mono.
          pose proof (extract_and_confine_work _ _ _ _ τ1 _ _ dwp' vr') as extr_tr. 
          eapply termrel₀_in_termrel in extr_tr.
          eapply (termrel_ectx' extr_tr); S.inferContext; U.inferContext; 
          crush; eauto using inject_value, protect_Value with eval.
          
          (* execute the applications *)
          intros w'' fw'' vs'' vu'' vr''.
          cbn.
          assert (w'' ≤ w) as fw2 by eauto with arith.
          pose proof (valrel_app (valrel_mono fw2 vr) vr'') as app_tr.
          eapply (termrel_ectx' app_tr); S.inferContext; U.inferContext; 
          crush; eauto using inject_value, protect_Value with eval.

          intros w''' fw''' vs''' vu''' vr'''.
          cbn.
          (* execute the inject/protect *)
          eapply termrel₀_in_termrel.
          eapply inject_and_protect_work; eauto using dwp_mono.
        }
    + (* tunit *)
      eapply termrel₀_antired_star.
      * eapply evalToStar.
        eapply (S.eval_ctx₀ S.phole); simpl;
        eauto using S.eval_beta.
      * eapply evalToStar.
        eapply U.eval₀_ctxeval.
        eapply U.eval_beta; eauto.
      * rewrite inUnitDwn_sub; cbn.

        eapply termrel₀_inUnitDwn; try assumption.
    + (* tbool *)
      eapply termrel₀_antired_star.
      * eapply evalToStar.
        eapply (S.eval_ctx₀ S.phole); simpl;
        eauto using S.eval_beta.
      * eapply evalToStar.
        eapply U.eval₀_ctxeval.
        eapply U.eval_beta; eauto.
      * rewrite inBoolDwn_sub; cbn.

        eapply termrel₀_inBoolDwn; try assumption.
    + (* tprod τ₁ τ₂ *)
      
      destruct (valrel_ptprod_inversion vr) as (vs₁ & vs₂ & vu₁ & vu₂ & ? & ? & ot₁ & ot₂ & vrs).
      subst.
      destruct ((fun x => x) vvs) as (vvs₁ & vvs₂).
      destruct ((fun x => x) vvu) as (vvu₁ & vvu₂).

      assert (0 + Nat.min 2 2 ≥ 1) as ineq by eauto with arith.
      
      eapply (termreli₀_antired 0 ineq).
      * (* beta-reduce *)
        eapply stepRel_step.
        eapply (S.eval_ctx₀ S.phole); simpl;
        eauto using S.eval_beta.
        rewrite inProdDwn_sub. cbn. repeat crushStlcSyntaxMatchH.
        rewrite ?inject_sub; cbn.

        (* project *)
        eapply stepRel_step.
        assert (S.eval₀ (S.proj₁ (S.pair vs₁ vs₂)) vs₁) as proj_eval₀ by crush.
        unfold inProdDwn.
        eapply (S.eval_from_eval₀ proj_eval₀); S.inferContext; crush;
        eauto using downgrade_value, inject_value.
        
        eapply stepRel_zero.

      * (* beta-reduce *)
        eapply stepRel_step.
        eapply U.eval₀_ctxeval.
        eapply U.eval_beta; eauto.
        cbn. repeat crushUtlcSyntaxMatchH. rewrite ?protect_sub.

        (* project *)
        eapply stepRel_step.
        assert (U.eval₀ (U.proj₁ (U.pair vu₁ vu₂)) vu₁) as proj_eval₀ by crush.
        eapply (U.ctxeval_from_eval₀ proj_eval₀); U.inferContext; crush;
        eauto using protect_Value.

        eapply stepRel_zero.
      * rewrite ?S.pctx_cat_app.
        cbn.
        destruct w.
        { eapply termrel₀_zero. }
        {
          assert (w < S w) as fw by eauto with arith.
          specialize (vrs w fw).
          destruct vrs as (vr₁ & vr₂).

          (* execute first inject/protects *)
          assert (dir_world_prec n w d p) as dwp' by eauto using dwp_mono.
          pose proof (inject_and_protect_work n w d p τ1 _ _ dwp' vr₁) as inj₁_tr. 

          change w with (lateri 1 (S w)) in inj₁_tr.
          assert (lev (S w) ≥ 1) by (unfold lev; omega).
          eapply (termreli₀_ectx' inj₁_tr); S.inferContext; U.inferContext;
          crush; eauto using downgrade_value.

          (* execute second projection *)
          intros vs₁' vu₁' vr₁'.
          destruct (valrel_implies_Value vr₁') as (? & ?).
          rewrite S.pctx_cat_app; cbn.
          eapply termreli₀_antired_star.
          - eapply evalToStar.
            assert (S.eval₀ (S.proj₂ (S.pair vs₁ vs₂)) vs₂) as proj_eval₀ by crush.
            unfold inProdDwn.
            eapply (S.eval_from_eval₀ proj_eval₀); S.inferContext; crush;
            eauto using downgrade_value, inject_value.
          - eapply evalToStar.
            assert (U.eval₀ (U.proj₂ (U.pair vu₁ vu₂)) vu₂) as proj_eval₀ by crush.
            eapply (U.ctxeval_from_eval₀ proj_eval₀); U.inferContext; crush;
            eauto using protect_Value.
          - rewrite ?S.pctx_cat_app, ?U.pctx_cat_app; cbn.

            (* execute second inject/protect *)
            pose proof (inject_and_protect_work n w d p τ2 _ _ dwp' vr₂) as inj₂_tr. 
            
            change w with (lateri 1 (S w)) in inj₂_tr.
            assert (lev (S w) ≥ 1) by (unfold lev; omega).
            eapply (termreli₀_ectx' inj₂_tr); S.inferContext; U.inferContext;
            crush; eauto using downgrade_value.
          
            intros vs₂' vu₂' vr₂'.
            rewrite ?S.pctx_cat_app; cbn.

            pose proof (valrel_pair' vr₁' vr₂') as vrp.
            eapply termrel₀_inProdDwn in vrp.
            eapply (termreli₀_dfc_mono vrp); eauto with arith.
            exact dwp.
        }
    + (* τ₁ ⊎ τ₂ *)
      rewrite ?protect_sub.