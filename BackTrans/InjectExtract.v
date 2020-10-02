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
Require Import BackTrans.UValHelpers2.

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
                       | tarr τ₁ τ₂ => S.abs τ₁ (S.app (extract n τ₂) (uvalApp n (S.var 1) (S.app (inject n τ₁) (S.var 0))))
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

Lemma extract_value {n τ} : S.Value (extract n τ).
Proof.
  (* exact I. *)
  (* Should be doable without the induction, but I don't see how *)
  induction τ; simpl; eauto with eval.
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

Lemma termrel₀_extract_unit {n w d p vs vu} :
  dir_world_prec n w d p →
  valrel d w (pEmulDV n p) vs vu →
  termrel₀ d w ptunit (caseUnitUp n vs) (U.seq vu U.unit).
Proof.
  intros dwp vr.
  unfold caseUnitUp.

  (* do the upgrade *)
  unfold caseUnitUp_pctx; rewrite S.pctx_cat_app; cbn.
  assert (trupg : termrel₀ d w (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works''.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel₀_ectx' trupg); S.inferContext; U.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros vs' vu' vr'.

  exact (termrel₀_caseUValUnit dwp vr').
Qed.
  
Lemma termrel₀_extract_bool {n w d p vs vu} :
  dir_world_prec n w d p →
  valrel d w (pEmulDV n p) vs vu →
  termrel₀ d w ptbool (caseBoolUp n vs) (U.ite vu U.true U.false).
Proof.
  intros dwp vr.
  unfold caseBoolUp.

  (* do the upgrade *)
  unfold caseBoolUp_pctx; rewrite S.pctx_cat_app; cbn.
  assert (trupg : termrel₀ d w (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works''.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel₀_ectx' trupg); S.inferContext; U.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros vs' vu' vr'.

  exact (termrel₀_caseUValBool dwp vr').
Qed.
  
Lemma termrel₀_extract_proj₁ {n w d p vs vu} :
  dir_world_prec n (S w) d p →
  valrel d (S w) (pEmulDV n p) vs vu →
  termrel₀ d w (pEmulDV n p) (S.proj₁ (caseProdUp n vs)) (U.proj₁ vu).
Proof.
  intros dwp tr.
  unfold caseProdUp.
  unfold caseProdUp_pctx; rewrite S.pctx_cat_app; cbn.

  (* execute the upgrade *)
  assert (trupg : termrel₀ d (S w) (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works''.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel₀_ectx''' trupg); S.inferContext; U.inferContext; crush.

  (* continuation bureaucracy *)
  intros vs' vu' vr'.
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValProd in vr'.
  fold (caseProd n vs').
  destruct vr' as [(vs'' & ? & es & vr'')|
                   [(? & div)|(? & div)]].
  - eapply termrel₀_antired_star_left.
    eapply (evalstar_ctx' es); S.inferContext; crush.
    simpl.
    eauto using termrel₀_proj₁, valrel_in_termrel₀.
  - subst; eapply dwp_invert_imprecise in dwp; subst.
    eapply termreli₀_div_lt.
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - eapply termreli₀_div_wrong.
    + eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      simpl.
      eapply evalToStar.
      eapply eval₀_to_eval.
      eauto with eval.
Qed.

Lemma termrel₀_extract_proj₂ {n w d p vs vu} :
  dir_world_prec n (S w) d p →
  valrel d (S w) (pEmulDV n p) vs vu →
  termrel₀ d w (pEmulDV n p) (S.proj₂ (caseProdUp n vs)) (U.proj₂ vu).
Proof.
  intros dwp tr.
  unfold caseProdUp.
  unfold caseProdUp_pctx; rewrite S.pctx_cat_app; cbn.

  (* execute the upgrade *)
  assert (trupg : termrel₀ d (S w) (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works''.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel₀_ectx''' trupg); S.inferContext; U.inferContext; crush.

  (* continuation bureaucracy *)
  intros vs' vu' vr'.
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValProd in vr'.
  fold (caseProd n vs').
  destruct vr' as [(vs'' & ? & es & vr'')|
                   [(? & div)|(? & div)]].
  - eapply termrel₀_antired_star_left.
    eapply (evalstar_ctx' es); S.inferContext; crush.
    simpl.
    eauto using termrel₀_proj₂, valrel_in_termrel₀.
  - subst; eapply dwp_invert_imprecise in dwp; subst.
    eapply termreli₀_div_lt.
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - eapply termreli₀_div_wrong.
    + eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      simpl.
      eapply evalToStar.
      eapply eval₀_to_eval.
      eauto with eval.
Qed.

Lemma termreli₀_extract_ptsum {n w d dfc p τ' vs₁ vu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n (S w) d p →
  valrel d (S w) (pEmulDV n p) vs₁ vu₁ →
  (forall vs₂ vu₂, 
                      valrel d w (pEmulDV n p) vs₂ vu₂ →
                      termreli₀ d dfc (S w) τ' (ts₂ [beta1 vs₂]) (tu₂ [beta1 vu₂])) →
  (forall vs₃ vu₃, 
                      valrel d w (pEmulDV n p) vs₃ vu₃ →
                      termreli₀ d dfc (S w) τ' (ts₃ [beta1 vs₃]) (tu₃ [beta1 vu₃])) →
  termreli₀ d dfc (S w) τ' (S.caseof (caseSumUp n vs₁) ts₂ ts₃) (U.caseof vu₁ tu₂ tu₃).
Proof.
  intros dwp vr₁ tr₂ tr₃. 
  unfold caseSumUp.
  unfold caseSumUp_pctx.
  rewrite S.pctx_cat_app; crush; cbn.

  (* evaluate upgrade *)
  assert (trupg : termrel₀ d (S w) (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs₁) vu₁)
    by eauto using upgrade_works''.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply termreli₀_dfc_mono in trupg; try omega.
  eapply (termrel₀_ectx' trupg); S.inferContext; U.inferContext; crush.

  (* continuation bureaucracy *)
  intros vs' vu' vr'.
  fold (caseSum n vs'); cbn.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValSum in vr'.
  destruct vr' as [(vs₁' & ? & es & vr₁')|
                   [(? & div)| (neql & neqr & div)]]; subst.

  - (* successful caseUValBool *)
    eapply termreli₀_antired_star.
    + eapply (evalstar_ctx' es); S.inferContext; crush.
    + eapply rt1n_refl. 
    + cbn.
      
      eapply termreli₀_caseof; eauto using valrel_in_termreli₀.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termreli₀_div_lt.
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - (* other cases *)
    eapply termreli₀_div_wrong.
    + eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      eapply evalToStar.
      eapply eval₀_to_eval.
      eauto with eval.
Qed.

Lemma inject_unit_works {n w d p vs vu} :
  dir_world_prec n w d p →
  valrel d w ptunit vs vu →
  termrel₀ d w (pEmulDV n p) (S.app (inject n tunit) vs) (U.app (protect tunit) vu).
Proof.
  intros dwp vr.
  destruct (valrel_implies_Value vr).
  eapply termrel₀_antired_star.
  - eapply evalToStar.
    eapply (S.eval_ctx₀ S.phole); simpl;
    eauto using S.eval_beta.
  - eapply evalToStar.
    eapply U.eval₀_ctxeval.
    eapply U.eval_beta; eauto.
  - rewrite inUnitDwn_sub; cbn.
        
    eapply termrel₀_inUnitDwn; now assumption.
Qed.

Lemma inject_bool_works {n w d p vs vu} :
  dir_world_prec n w d p →
  valrel d w ptbool vs vu →
  termrel₀ d w (pEmulDV n p) (S.app (inject n tbool) vs) (U.app (protect tbool) vu).
Proof.
  intros dwp vr.
  destruct (valrel_implies_Value vr).
  eapply termrel₀_antired_star.
  - eapply evalToStar.
    eapply (S.eval_ctx₀ S.phole); simpl;
    eauto using S.eval_beta.
  - eapply evalToStar.
    eapply U.eval₀_ctxeval.
    eapply U.eval_beta; eauto.
  - rewrite inBoolDwn_sub; cbn.
    eapply termrel₀_inBoolDwn; now assumption.
Qed.


Lemma inject_tarr_works {n w d p τ₁ τ₂ vs vu} :
  dir_world_prec n w d p →
  valrel d w (embed (τ₁ ⇒ τ₂)) vs vu →
  (forall {w' vs' vu'}, w' < w →
              valrel d w' (pEmulDV n p) vs' vu' →
              termrel₀ d w' (embed τ₁) (S.app (extract n τ₁) vs') (U.app (confine τ₁) vu')) →
  (forall {w' vs' vu'}, w' < w →
              valrel d w' (embed τ₂) vs' vu' →
              termrel₀ d w' (pEmulDV n p) (S.app (inject n τ₂) vs') (U.app (protect τ₂) vu')) →
  termrel₀ d w (pEmulDV n p) (S.app (inject n (τ₁ ⇒ τ₂)) vs) (U.app (protect (τ₁ ⇒ τ₂)) vu).
Proof.
  intros dwp vr extr₁ inj₂.
  destruct (valrel_implies_Value vr) as [? ?].
  destruct (valrel_implies_OfType vr) as [[? tvs] [closed_vu ?]].
  eapply termrel₀_antired_star.
  - eapply evalToStar.
    eapply (S.eval_ctx₀ S.phole); simpl;
    eauto using S.eval_beta.
  - eapply evalToStar.
    eapply U.eval₀_ctxeval.
    eapply U.eval_beta; eauto.
  - cbn.
    rewrite inArrDwn_sub, protect_sub, confine_sub. 
    crushTyping.
    rewrite inject_sub, extract_sub; cbn.
    crushUtlcScoping.
    rewrite ?protect_sub, ?confine_sub.

    eapply termrel₀_inArrDwn; try assumption.
    
    change (UVal n) with (repEmul (pEmulDV n p)). 
    eapply valrel_lambda. 
    + eapply OfType_lambda; auto.
      * crushUtlcScoping; eauto using protect_closed, confine_closed.
      * crushTyping; rewrite repEmul_embed_leftinv; eauto using injectT, extractT.
    + intros w' vs' vu' fw' vr'.
      cbn.
      crushUtlcScoping.
      crushTyping.
      rewrite ?protect_sub, ?confine_sub.
      rewrite ?inject_sub, ?extract_sub.
      rewrite ?(wsClosed_invariant (wt_implies_ws tvs)).
      rewrite ?(wsClosed_invariant closed_vu).

      (* execute the extract/confine *)
      assert (dir_world_prec n w' d p) as dwp' by eauto using dwp_mono.
      pose proof (extr₁ _ _ _ fw' vr') as extr_tr. 
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
      eapply inj₂; eauto using dwp_mono with arith.
Qed.

Lemma inject_tprod_works {n w d p τ₁ τ₂ vs vu} :
  dir_world_prec n w d p →
  valrel d w (embed (tprod τ₁ τ₂)) vs vu →
  (forall {w' vs' vu'}, w' < w →
              valrel d w' (embed τ₁) vs' vu' →
              termrel₀ d w' (pEmulDV n p) (S.app (inject n τ₁) vs') (U.app (protect τ₁) vu')) →
  (forall {w' vs' vu'}, w' < w →
              valrel d w' (embed τ₂) vs' vu' →
              termrel₀ d w' (pEmulDV n p) (S.app (inject n τ₂) vs') (U.app (protect τ₂) vu')) →
  termrel₀ d w (pEmulDV n p) (S.app (inject n (tprod τ₁ τ₂)) vs) (U.app (protect (tprod τ₁ τ₂)) vu).
Proof.
  intros dwp vr inj₁ inj₂.
  destruct (valrel_implies_Value vr) as [vvs vvu].
  destruct (valrel_implies_OfType vr) as [[? tvs] [closed_vu ?]].

  destruct (valrel_ptprod_inversion vr) as (vs₁ & vs₂ & vu₁ & vu₂ & ? & ? & ot₁ & ot₂ & vrs).
  subst.
  destruct ((fun x => x) vvs) as (vvs₁ & vvs₂).
  destruct ((fun x => x) vvu) as (vvu₁ & vvu₂).

  assert (0 + Nat.min 2 2 ≥ 1) as ineq by eauto with arith.
  
  eapply (termreli₀_antired 0 ineq).
  - (* beta-reduce *)
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

  - (* beta-reduce *)
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
  - rewrite ?S.pctx_cat_app.
    cbn.
    destruct w.
    + eapply termrel₀_zero.
    + assert (w < S w) as fw by eauto with arith.
      specialize (vrs w fw).
      destruct vrs as (vr₁ & vr₂).

      (* execute first inject/protects *)
      assert (dir_world_prec n w d p) as dwp' by eauto using dwp_mono.
      pose proof (inj₁ _ _ _ fw vr₁) as inj₁_tr. 

      change w with (lateri 1 (S w)) in inj₁_tr.
      assert (lev (S w) ≥ 1) by (unfold lev; omega).
      eapply (termreli₀_ectx' inj₁_tr); S.inferContext; U.inferContext;
      crush; eauto using downgrade_value.

      (* execute second projection *)
      intros vs₁' vu₁' vr₁'.
      destruct (valrel_implies_Value vr₁') as (? & ?).
      rewrite S.pctx_cat_app; cbn.
      eapply termreli₀_antired_star.
      * eapply evalToStar.
        assert (S.eval₀ (S.proj₂ (S.pair vs₁ vs₂)) vs₂) as proj_eval₀ by crush.
        unfold inProdDwn.
        eapply (S.eval_from_eval₀ proj_eval₀); S.inferContext; crush;
        eauto using downgrade_value, inject_value.
      * eapply evalToStar.
        assert (U.eval₀ (U.proj₂ (U.pair vu₁ vu₂)) vu₂) as proj_eval₀ by crush.
        eapply (U.ctxeval_from_eval₀ proj_eval₀); U.inferContext; crush;
        eauto using protect_Value.
      * rewrite ?S.pctx_cat_app, ?U.pctx_cat_app; cbn.

        (* execute second inject/protect *)
        pose proof (inj₂ _ _ _ fw vr₂) as inj₂_tr. 
        
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
Qed.

Lemma inject_tsum_works {n w d p τ₁ τ₂ vs vu} :
  dir_world_prec n w d p →
  valrel d w (embed (tsum τ₁ τ₂)) vs vu →
  (forall {w' vs' vu'}, w' < w →
              valrel d w' (embed τ₁) vs' vu' →
              termrel₀ d w' (pEmulDV n p) (S.app (inject n τ₁) vs') (U.app (protect τ₁) vu')) →
  (forall {w' vs' vu'}, w' < w →
              valrel d w' (embed τ₂) vs' vu' →
              termrel₀ d w' (pEmulDV n p) (S.app (inject n τ₂) vs') (U.app (protect τ₂) vu')) →
  termrel₀ d w (pEmulDV n p) (S.app (inject n (tsum τ₁ τ₂)) vs) (U.app (protect (tsum τ₁ τ₂)) vu).
Proof.
  intros dwp vr inj₁ inj₂.
  destruct (valrel_implies_Value vr) as [vvs vvu].
  destruct (valrel_implies_OfType vr) as [[? tvs] [closed_vu ?]].

  rewrite ?protect_sub.

  destruct w; try eapply termrel₀_zero.
  assert (w < S w) as fw by eauto with arith.
  assert (dir_world_prec n w d p) as dwp' by eauto using dwp_mono.
  
  destruct (valrel_ptsum_inversion vr) as (vs' & vu' & [(? & ? & ot' & vrs)|(? & ? & ot' & vrs) ]);
    specialize (vrs w fw);
    subst; cbn in vvs;
    assert (0 + Nat.min 2 2 ≥ 1) as ineq by eauto with arith.
  - eapply (termreli₀_antired 0 ineq).
    + (* beta-reduce *)
      eapply stepRel_step.
      eapply (S.eval_ctx₀ S.phole); simpl;
      eauto using S.eval_beta.
      rewrite inSumDwn_sub. cbn. repeat crushStlcSyntaxMatchH.
      rewrite ?inject_sub; cbn.

      (* execute the pattern match *)
      eapply stepRel_step.
      assert (S.eval₀ (S.caseof (S.inl vs') (S.inl (S.app (inject n τ₁) (S.var 0))) (S.inr (S.app (inject n τ₂) (S.var 0)))) (S.inl (S.app (inject n τ₁) (S.var 0)))[beta1 vs']) as caseof_eval₀ by crush.
      unfold inSumDwn.
      eapply (S.eval_from_eval₀ caseof_eval₀); S.inferContext; crush;
      eauto using downgrade_value, inject_value.

      eapply stepRel_zero.
    + (* beta-reduce *)
      eapply stepRel_step.
      eapply U.eval₀_ctxeval.
      eapply U.eval_beta; eauto.
      cbn. repeat crushUtlcSyntaxMatchH. rewrite ?protect_sub.

      (* execute the pattern match *)
      eapply stepRel_step.
      assert (U.eval₀ (U.caseof (U.inl vu') (U.inl (U.app (protect τ₁) (U.var 0)))
                                (U.inr (U.app (protect τ₂) (U.var 0)))) (U.inl (U.app (protect τ₁) (U.var 0))) [beta1 vu']) as proj_eval₀ by crush.
      eapply (U.ctxeval_from_eval₀ proj_eval₀); U.inferContext; crush;
      eauto using protect_Value.
      
      eapply stepRel_zero.
    + crush.
      rewrite ?inject_sub, ?protect_sub; cbn.

      (* execute inject/protect *)
      pose proof (inj₁ _ _ _ fw vrs) as inj_tr. 
      change w with (lateri 1 (S w)) in inj_tr.
      assert (lev (S w) ≥ 1) by (unfold lev; omega).
      eapply (termreli₀_ectx' inj_tr); S.inferContext; U.inferContext;
      crush; eauto using downgrade_value.

      (* and finish up *)
      intros vs'' vu'' vr''.
      destruct (valrel_implies_OfType vr'') as ((? & ?) & (? & ?)).
      rewrite S.pctx_cat_app; cbn.

      eapply valrel_inl' in vr''.
      eapply termrel₀_inSumDwn in vr''; try assumption.
      refine (termreli₀_dfc_mono vr'' _); eauto with arith.
  - eapply (termreli₀_antired 0 ineq).
    + (* beta-reduce *)
      eapply stepRel_step.
      eapply (S.eval_ctx₀ S.phole); simpl;
      eauto using S.eval_beta.
      rewrite inSumDwn_sub. cbn. repeat crushStlcSyntaxMatchH.
      rewrite ?inject_sub; cbn.

      (* execute the pattern match *)
      eapply stepRel_step.
      assert (S.eval₀ (S.caseof (S.inr vs') (S.inl (S.app (inject n τ₁) (S.var 0))) (S.inr (S.app (inject n τ₂) (S.var 0)))) (S.inr (S.app (inject n τ₂) (S.var 0)))[beta1 vs']) as caseof_eval₀ by crush.
      unfold inSumDwn.
      eapply (S.eval_from_eval₀ caseof_eval₀); S.inferContext; crush;
      eauto using downgrade_value, inject_value.

      eapply stepRel_zero.
    + (* beta-reduce *)
      eapply stepRel_step.
      eapply U.eval₀_ctxeval.
      eapply U.eval_beta; eauto.
      cbn. repeat crushUtlcSyntaxMatchH. rewrite ?protect_sub.

      (* execute the pattern match *)
      eapply stepRel_step.
      assert (U.eval₀ (U.caseof (U.inr vu') (U.inl (U.app (protect τ₁) (U.var 0)))
                                (U.inr (U.app (protect τ₂) (U.var 0)))) (U.inr (U.app (protect τ₂) (U.var 0))) [beta1 vu']) as proj_eval₀ by crush.
      eapply (U.ctxeval_from_eval₀ proj_eval₀); U.inferContext; crush;
      eauto using protect_Value.
      
      eapply stepRel_zero.
    + crush.
      rewrite ?inject_sub, ?protect_sub; cbn.

      (* execute inject/protect *)
      pose proof (inj₂ _ _ _ fw vrs) as inj_tr. 
      change w with (lateri 1 (S w)) in inj_tr.
      assert (lev (S w) ≥ 1) by (unfold lev; omega).
      eapply (termreli₀_ectx' inj_tr); S.inferContext; U.inferContext;
      crush; eauto using downgrade_value.

      (* and finish up *)
      intros vs'' vu'' vr''.
      destruct (valrel_implies_OfType vr'') as ((? & ?) & (? & ?)).
      rewrite S.pctx_cat_app; cbn.

      eapply valrel_inr' in vr''.
      eapply termrel₀_inSumDwn in vr''; try assumption.
      refine (termreli₀_dfc_mono vr'' _); eauto with arith.
Qed.

Lemma extract_tunit_works {n w d p vs vu} :
  dir_world_prec n w d p →
  valrel d w (pEmulDV n p) vs vu →
  termrel₀ d w (embed tunit) (S.app (extract n tunit) vs) (U.app (confine tunit) vu).
Proof.
  intros dwp vr.
  destruct (valrel_implies_Value vr) as [vvs vvu].
  destruct (valrel_implies_OfType vr) as [[? tvs] [closed_vu ?]].

  eapply termrel₀_antired_star.
  - eapply evalToStar.
    eapply (S.eval_ctx₀ S.phole); simpl;
    eauto using S.eval_beta.
  - eapply evalToStar.
    eapply U.eval₀_ctxeval.
    eapply U.eval_beta; eauto.
  - rewrite caseUnitUp_sub; cbn.
    eapply termrel₀_extract_unit; try eassumption.
Qed.

Lemma extract_tbool_works {n w d p vs vu} :
  dir_world_prec n w d p →
  valrel d w (pEmulDV n p) vs vu →
  termrel₀ d w (embed tbool) (S.app (extract n tbool) vs) (U.app (confine tbool) vu).
Proof.
  intros dwp vr.
  destruct (valrel_implies_Value vr) as [vvs vvu].
  destruct (valrel_implies_OfType vr) as [[? tvs] [closed_vu ?]].

  eapply termrel₀_antired_star.
  - eapply evalToStar.
    eapply (S.eval_ctx₀ S.phole); simpl;
    eauto using S.eval_beta.
  - eapply evalToStar.
    eapply U.eval₀_ctxeval.
    eapply U.eval_beta; eauto.
  - rewrite caseBoolUp_sub; cbn.
    eapply termrel₀_extract_bool; try eassumption.
Qed.

Lemma extract_tarr_works {n w d p τ₁ τ₂ vs vu} :
  dir_world_prec n w d p →
  valrel d w (pEmulDV n p) vs vu →
  (forall w' vs' vu', w' < w → 
                      valrel d w' (embed τ₁) vs' vu' →
                      termrel₀ d w' (pEmulDV n p) (S.app (inject n τ₁) vs') (U.app (protect τ₁) vu')) →
  (forall w' vs' vu', w' < w → 
                      valrel d w' (pEmulDV n p) vs' vu' →
                      termrel₀ d w' (embed τ₂) (S.app (extract n τ₂) vs') (U.app (confine τ₂) vu')) →
  termrel₀ d w (embed (tarr τ₁ τ₂)) (S.app (extract n (tarr τ₁ τ₂)) vs) (U.app (confine (tarr τ₁ τ₂)) vu).
Proof.
  intros dwp vr inj₁ extr₂.
  destruct (valrel_implies_Value vr) as [vvs vvu].
  destruct (valrel_implies_OfType vr) as [[? tvs] [closed_vu ?]].
  eapply termrel₀_antired_star.
  - eapply evalToStar.
    eapply (S.eval_ctx₀ S.phole); simpl;
    eauto using S.eval_beta.
  - eapply evalToStar.
    eapply U.eval₀_ctxeval.
    eapply U.eval_beta; eauto.
  - cbn.
    rewrite protect_sub, confine_sub. 
    crushTyping.
    rewrite uvalApp_sub; crushTyping.
    rewrite inject_sub, extract_sub; cbn.
    crushUtlcScoping.
    rewrite ?protect_sub, ?confine_sub.

    eapply valrel_in_termrel₀.
    replace τ₁ with (repEmul (embed τ₁)) at 2 by eapply repEmul_embed_leftinv.
    eapply valrel_lambda.
    + eapply OfType_lambda; crushUtlcScoping;
      rewrite ?repEmul_embed_leftinv;
      eauto using protect_closed, confine_closed, extractT, injectT, uvalApp_T with typing.
    + intros w' vs' vu' fw vr'.
      cbn.
      crushUtlcScoping.
      crushTyping.
      rewrite uvalApp_sub.
      cbn; crushUtlcScoping; crushTyping.
      rewrite ?protect_sub, ?confine_sub.
      rewrite ?inject_sub, ?extract_sub.
      rewrite ?(wsClosed_invariant (wt_implies_ws tvs)).
      rewrite ?(wsClosed_invariant closed_vu).

      assert (dir_world_prec n w' d p) as dwp' by eauto using dwp_mono.
      assert (termrel d w' (pEmulDV n p) (uvalApp n vs (S.app (inject n τ₁) vs')) (U.app vu (U.app (protect τ₁) vu'))) as uvalApp_tr.
      * eapply termrel_uvalApp; eauto using valrel_mono, valrel_in_termrel.
        intros w'' fw'.
        (* execute the inject/protect *)
        eapply termrel₀_in_termrel.
        eapply inj₁; eauto using valrel_mono, dwp_mono with arith.
      * eapply (termrel_ectx' uvalApp_tr); S.inferContext; U.inferContext; 
        crush; eauto using extract_value, confine_Value with eval.
        
        intros w'' fw'' vs'' vu'' vr''.
        cbn.
        
        eapply termrel₀_in_termrel.
        eapply extr₂; eauto using valrel_mono, dwp_mono with arith.
Qed.
    
Lemma extract_tprod_works {n w d p τ₁ τ₂ vs vu} :
  dir_world_prec n w d p →
  valrel d w (pEmulDV n p) vs vu →
  (forall w' vs' vu', w' < w → 
                      valrel d w' (pEmulDV n p) vs' vu' →
                      termrel₀ d w' (embed τ₁) (S.app (extract n τ₁) vs') (U.app (confine τ₁) vu')) →
  (forall w' vs' vu', w' < w → 
                      valrel d w' (pEmulDV n p) vs' vu' →
                      termrel₀ d w' (embed τ₂) (S.app (extract n τ₂) vs') (U.app (confine τ₂) vu')) →
  termrel₀ d w (embed (tprod τ₁ τ₂)) (S.app (extract n (tprod τ₁ τ₂)) vs) (U.app (confine (tprod τ₁ τ₂)) vu).
Proof.
  intros dwp vr extr₁ extr₂.
  destruct (valrel_implies_Value vr) as [vvs vvu].
  destruct (valrel_implies_OfType vr) as [[? tvs] [closed_vu ?]].

  assert (0 + Nat.min 1 1 ≥ 1) as ineq by eauto with arith.
  
  eapply (termreli₀_antired 0 ineq).
  * (* beta-reduce *)
    eapply stepRel_step.
    eapply (S.eval_ctx₀ S.phole); simpl;
    eauto using S.eval_beta.
    cbn. crushTyping. rewrite caseProdUp_sub. cbn. repeat crushStlcSyntaxMatchH.
    rewrite ?extract_sub; cbn.

    eapply stepRel_zero.

  * (* beta-reduce *)
    eapply stepRel_step.
    eapply U.eval₀_ctxeval.
    eapply U.eval_beta; eauto.
    cbn. repeat crushUtlcSyntaxMatchH. rewrite ?confine_sub.

    eapply stepRel_zero.
  * destruct w; try eapply termrel₀_zero.
    assert (w < S w) as fw by eauto with arith.

    (* execute proj₁s *)
    pose proof (termrel₀_extract_proj₁ dwp vr) as proj₁_tr. 
    change w with (lateri 1 (S w)) in proj₁_tr.
    eapply (termreli₀_ectx' proj₁_tr); S.inferContext; U.inferContext; crush; unfold lev in *; eauto using extract_value, confine_Value with arith.

    (* continuation boilerplate *)
    intros vs₁' vu₁' vr₁'.
    rewrite U.pctx_cat_app; cbn.
    
    (* execute first extract/confine *)
    assert (dir_world_prec n w d p) as dwp' by eauto using dwp_mono.
    pose proof (extr₁ _ _ _ fw vr₁') as extract₁_tr.
    change w with (lateri 1 (S w)) in extract₁_tr.
    eapply (termreli₀_ectx' extract₁_tr); S.inferContext; U.inferContext; crush; unfold lev; eauto with arith.

    (* continuation boilerplate *)
    intros vs₁'' vu₁'' vr₁''.
    rewrite U.pctx_cat_app; cbn.
    destruct (valrel_implies_Value vr₁'').
    
    (* execute proj₂s *)
    pose proof (termrel₀_extract_proj₂ dwp vr) as proj₂_tr. 
    change w with (lateri 1 (S w)) in proj₂_tr.
    eapply (termreli₀_ectx' proj₂_tr); S.inferContext; U.inferContext; crush; unfold lev in *; eauto using extract_value, confine_Value with arith.

    (* continuation boilerplate *)
    intros vs₂' vu₂' vr₂'.
    rewrite U.pctx_cat_app; cbn.
    
    (* execute first extract/confine *)
    pose proof (extr₂ _ _ _ fw vr₂') as extract₂_tr.
    change w with (lateri 1 (S w)) in extract₂_tr.
    eapply (termreli₀_ectx' extract₂_tr); S.inferContext; U.inferContext; crush; unfold lev; eauto with arith.

    (* continuation boilerplate *)
    intros vs₂'' vu₂'' vr₂''.
    rewrite U.pctx_cat_app; cbn.

    eapply valrel_in_termreli₀.
    eapply valrel_pair'; assumption.
Qed.

Lemma extract_tsum_works {n w d p τ₁ τ₂ vs vu} :
  dir_world_prec n w d p →
  valrel d w (pEmulDV n p) vs vu →
  (forall w' vs' vu', w' < w → 
                      valrel d w' (pEmulDV n p) vs' vu' →
                      termrel₀ d w' (embed τ₁) (S.app (extract n τ₁) vs') (U.app (confine τ₁) vu')) →
  (forall w' vs' vu', w' < w → 
                      valrel d w' (pEmulDV n p) vs' vu' →
                      termrel₀ d w' (embed τ₂) (S.app (extract n τ₂) vs') (U.app (confine τ₂) vu')) →
  termrel₀ d w (embed (tsum τ₁ τ₂)) (S.app (extract n (tsum τ₁ τ₂)) vs) (U.app (confine (tsum τ₁ τ₂)) vu).
Proof.
  intros dwp vr extr₁ extr₂.
  destruct (valrel_implies_Value vr) as [vvs vvu].
  destruct (valrel_implies_OfType vr) as [[? tvs] [closed_vu ?]].

  rewrite ?confine_sub.

  assert (0 + Nat.min 1 1 ≥ 1) as ineq by eauto with arith.
  
  eapply (termreli₀_antired 0 ineq).
  - (* beta-reduce *)
    eapply stepRel_step.
    eapply (S.eval_ctx₀ S.phole); simpl;
    eauto using S.eval_beta.
    cbn. crushTyping. rewrite caseSumUp_sub. cbn. repeat crushStlcSyntaxMatchH.
    rewrite ?extract_sub; cbn.

    eapply stepRel_zero.

  - (* beta-reduce *)
    eapply stepRel_step.
    eapply U.eval₀_ctxeval.
    eapply U.eval_beta; eauto.
    cbn. repeat crushUtlcSyntaxMatchH. rewrite ?confine_sub.

    eapply stepRel_zero.
  - destruct w; try eapply termrel₀_zero.
    assert (w < S w) as fw by eauto with arith.
    eapply termreli₀_extract_ptsum; try eassumption.
    + intros vs₂ vu₂ vr₂.
      cbn. crush. rewrite confine_sub, extract_sub.

      assert (dir_world_prec n w d p) as dwp' by eauto using dwp_mono.
      pose proof (extr₁ _ _ _ fw vr₂) as extract_tr.
      change w with (lateri 1 (S w)) in extract_tr.
      eapply (termreli₀_ectx' extract_tr); S.inferContext; U.inferContext; crush; unfold lev; eauto with arith.

      intros vs₂' vu₂' vr₂'.
      cbn.
      eauto using valrel_in_termreli₀, valrel_inl'.
    + intros vs₃ vu₃ vr₃.
      cbn. crush. rewrite confine_sub, extract_sub.

      assert (dir_world_prec n w d p) as dwp' by eauto using dwp_mono.
      pose proof (extr₂ _ _ _ fw vr₃) as extract_tr.
      change w with (lateri 1 (S w)) in extract_tr.
      eapply (termreli₀_ectx' extract_tr); S.inferContext; U.inferContext; crush; unfold lev; eauto with arith.

      intros vs₃' vu₃' vr₃'.
      cbn.
      eauto using valrel_in_termreli₀, valrel_inr'.
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
      eapply inject_tarr_works; 
      eauto using dwp_mono.
    + (* tunit *)
      eapply inject_unit_works; now assumption.
    + (* tbool *)
      eapply inject_bool_works; now assumption.
    + (* tprod τ₁ τ₂ *)
      eapply inject_tprod_works; 
      eauto using dwp_mono.
    + (* τ₁ ⊎ τ₂ *)
      eapply inject_tsum_works; 
      eauto using dwp_mono.
  - (* extract *)
    revert n w vs vu.
    induction τ;
      intros n w vs vu dwp vr; 
      destruct (valrel_implies_OfType vr) as ((_ & tvs) & (closed_vu & _));
      destruct (valrel_implies_Value vr) as (vvs & vvu);
      simpl.
    + (* τ₁ ⇒ τ₂ *) 
      eapply extract_tarr_works; 
      eauto using dwp_mono.
    + (* tunit *)
      eapply extract_tunit_works; 
      eauto using dwp_mono.
    + (* tbool *)
      eapply extract_tbool_works; 
      eauto using dwp_mono.
    + (* tprod τ₁ τ₂ *)
      eapply extract_tprod_works; 
      eauto using dwp_mono.
      
    + (* τ₁ ⊎ τ₂ *)
      eapply extract_tsum_works; 
      eauto using dwp_mono.
Qed.

Lemma inject_works_open {d n m τ ts tu Γ p} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : embed τ ⟫ →
  ⟪ Γ ⊩ S.app (inject n τ) ts ⟦ d , m ⟧ U.app (protect τ) tu : pEmulDV n p ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & lr).
  unfold OpenLRCtxN; split; [|split].
  - crushTyping. 
    rewrite repEmul_embed_leftinv.
    eauto using injectT.
  - crushUtlcScoping; eauto using protect_closed.
  - intros w wm γs γu envrel.
    specialize (lr w wm γs γu envrel).

    cbn; crushTyping; crushUtlcScoping.
    rewrite inject_sub, protect_sub.

    eapply (termrel_ectx' lr); S.inferContext; U.inferContext; 
    crush; eauto using inject_value, protect_Value.

    intros w' fw vs vu vr.
    cbn.
    eapply termrel₀_in_termrel.
    eapply inject_and_protect_work; eauto using dwp_mono.
Qed.

Lemma extract_works_open {d n m τ ts tu Γ p} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ S.app (extract n τ) ts ⟦ d , m ⟧ U.app (confine τ) tu : embed τ ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & lr).
  unfold OpenLRCtxN; split; [|split].
  - crushTyping.
    rewrite repEmul_embed_leftinv.
    eauto using extractT.
  - crushUtlcScoping; eauto using confine_closed.
  - intros w wm γs γu envrel.
    specialize (lr w wm γs γu envrel).

    cbn; crushTyping; crushUtlcScoping.
    rewrite extract_sub, confine_sub.

    eapply (termrel_ectx' lr); S.inferContext; U.inferContext;
    crush; eauto using extract_value, confine_Value.

    intros w' fw vs vu vr.
    cbn.
    eapply termrel₀_in_termrel.
    eapply extract_and_confine_work.
    eauto using dwp_mono.
    assumption.
Qed.
