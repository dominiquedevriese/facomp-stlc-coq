Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import BackTrans.UValHelpers.
Require Import Stlc.SpecTyping.
Require Import Stlc.StlcOmega.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import Utlc.DecideEval.
Require Import LogRel.PseudoType.
Require Import LogRel.LemmasPseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import LogRel.LemmasIntro.
Require Import LogRel.LemmasInversion.
Require Import Omega.
Require Import Db.Lemmas.
Require Import UVal.UVal.
Require Utlc.Fix.
Require Omega.

Fixpoint emulate (n : nat) (t : U.UTm) : S.Tm :=
  match t with
    | U.wrong => stlcOmega (UVal n)
    | U.var i => S.var i
    | U.abs t => inArrDwn n (S.abs (UVal n) (emulate n t))
    | U.app t₁ t₂ => S.app (caseArrUp n (emulate n t₁)) (emulate n t₂)
    | U.unit => inUnitDwn n S.unit
    | U.true => inBoolDwn n S.true
    | U.false => inBoolDwn n S.false
    | U.ite t₁ t₂ t₃ => S.ite (caseBoolUp n (emulate n t₁)) (emulate n t₂) (emulate n t₃)
    | U.pair t₁ t₂ => inProdDwn n (S.pair (emulate n t₁) (emulate n t₂))
    | U.proj₁ t => S.proj₁ (caseProdUp n (emulate n t))
    | U.proj₂ t => S.proj₂ (caseProdUp n (emulate n t))
    | U.inl t => inSumDwn n (S.inl (emulate n t))
    | U.inr t => inSumDwn n (S.inr (emulate n t))
    | U.caseof t₁ t₂ t₃ => S.caseof (caseSumUp n (emulate n t₁)) (emulate n t₂) (emulate n t₃)
    | U.seq t₁ t₂ => S.seq (caseUnitUp n (emulate n t₁)) (emulate n t₂)
  end.

Fixpoint emulate_pctx (n : nat) (C : U.PCtx) : S.PCtx :=
  match C with
    | U.phole => S.phole
    | U.pabs C => S.pctx_cat (S.pabs (UVal n) (emulate_pctx n C)) (inArrDwn_pctx n)
    | U.papp₁ C t₂ => S.papp₁ (S.pctx_cat (emulate_pctx n C) (caseArrUp_pctx n)) (emulate n t₂)
    | U.papp₂ t₁ C => S.papp₂ (caseArrUp n (emulate n t₁)) (emulate_pctx n C)
    | U.pite₁ C₁ t₂ t₃ => S.pite₁ (S.pctx_cat (emulate_pctx n C₁) (caseBoolUp_pctx n)) (emulate n t₂) (emulate n t₃)
    | U.pite₂ t₁ C₂ t₃ => S.pite₂ (caseBoolUp n (emulate n t₁)) (emulate_pctx n C₂) (emulate n t₃)
    | U.pite₃ t₁ t₂ C₃ => S.pite₃ (caseBoolUp n (emulate n t₁)) (emulate n t₂) (emulate_pctx n C₃)
    | U.ppair₁ C₁ t₂ => S.pctx_cat (S.ppair₁ (emulate_pctx n C₁) (emulate n t₂)) (inProdDwn_pctx n)
    | U.ppair₂ t₁ C₂ => S.pctx_cat (S.ppair₂ (emulate n t₁) (emulate_pctx n C₂)) (inProdDwn_pctx n) 
    | U.pproj₁ C => S.pproj₁ (S.pctx_cat (emulate_pctx n C) (caseProdUp_pctx n))
    | U.pproj₂ C => S.pproj₂ (S.pctx_cat (emulate_pctx n C) (caseProdUp_pctx n))
    | U.pinl C => S.pctx_cat (S.pinl (emulate_pctx n C)) (inSumDwn_pctx n)
    | U.pinr C => S.pctx_cat (S.pinr (emulate_pctx n C)) (inSumDwn_pctx n)
    | U.pcaseof₁ C₁ t₂ t₃ => S.pcaseof₁ (S.pctx_cat (emulate_pctx n C₁) (caseSumUp_pctx n)) (emulate n t₂) (emulate n t₃)
    | U.pcaseof₂ t₁ C₂ t₃ => S.pcaseof₂ (caseSumUp n (emulate n t₁)) (emulate_pctx n C₂) (emulate n t₃)
    | U.pcaseof₃ t₁ t₂ C₃ => S.pcaseof₃ (caseSumUp n (emulate n t₁)) (emulate n t₂) (emulate_pctx n C₃)
    | U.pseq₁ C₁ t₂ => S.pseq₁ (S.pctx_cat (emulate_pctx n C₁) (caseUnitUp_pctx n)) (emulate n t₂)
    | U.pseq₂ t₁ C₂ => S.pseq₂ (caseUnitUp n (emulate n t₁)) (emulate_pctx n C₂)
  end.

Fixpoint toUVals n (Γ : Dom) : Env :=
  match Γ with
      0 => S.empty
    | S Γ' => toUVals n Γ' ▻ UVal n
  end.

Lemma toUVals_entry {n Γ i} :
  Γ ∋ i → ⟪ i : UVal n ∈ toUVals n Γ ⟫.
Proof.
  induction 1; simpl; crushTyping.
Qed.

Lemma emulate_T {n Γ t} :
  ⟨ Γ ⊢ t ⟩ →
  ⟪ toUVals n Γ ⊢ emulate n t : UVal n ⟫.
Proof.
  induction 1; unfold emulate;
  eauto using stlcOmegaT, toUVals_entry with typing uval_typing.
Qed.

Lemma emulate_T' {γ t n} :
  ⟨ S γ ⊢ t ⟩ →
  ⟪ toUVals n γ ▻ UVal n ⊢ emulate n t : UVal n ⟫.
Proof.
  change (toUVals n γ ▻ UVal n) with (toUVals n (S γ)).
  eauto using emulate_T.
Qed.

Lemma emulate_pctx_T {n Γ Γ' C} :
  ⟨ ⊢ C : Γ → Γ' ⟩ →
  ⟪ ⊢ emulate_pctx n C : toUVals n Γ , UVal n → toUVals n Γ' , UVal n ⟫.
Proof.
  induction 1; unfold emulate_pctx;
  eauto using toUVals_entry, inUnitDwn_pctx_T, inBoolDwn_pctx_T, inProdDwn_pctx_T, inSumDwn_pctx_T, inArrDwn_pctx_T, caseUnitUp_pctx_T, caseBoolUp_pctx_T, caseProdUp_pctx_T, caseSumUp_pctx_T, caseArrUp_pctx_T, emulate_T, emulate_T', PCtxTyping, caseSumUp_T with typing uval_typing.
Qed.

Local Ltac crush :=
  repeat (repeat crushUtlcSyntaxMatchH; 
          repeat crushStlcSyntaxMatchH; 
          repeat crushStlcEval; 
          repeat crushDbSyntaxMatchH;
          repeat crushDbLemmasMatchH;
          repeat crushDbLemmasRewriteH;
          try assumption;
          crushOfType;
          trivial;
          eauto using caseUnit_pctx_ECtx, caseBool_pctx_ECtx, caseProd_pctx_ECtx, caseSum_pctx_ECtx, caseArr_pctx_ECtx, upgrade_value, downgrade_value with typing
         ).

Lemma compat_emul_abs {n m d p Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ p▻ pEmulDV n p ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ inArrDwn n (S.abs (UVal n) ts) ⟦ d , m ⟧ U.abs tu : pEmulDV n p ⟫.
Proof.
  intros dwp [ty tr].
  split.
  - eauto using inArrDwn_T with typing uval_typing.
  - intros w wn γs γu envrel.

    assert (OfType (ptarr (pEmulDV n p) (pEmulDV n p))
                   (S.abs (repEmul (pEmulDV n p)) 
                          (ts [γs↑])) (U.abs (tu [γu↑])))
      by (pose proof (envrel_implies_WtSub envrel);
          crush).

    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    rewrite inArrDwn_sub.
    eapply termrel_inArrDwn; try assumption.

    change (UVal n) with (repEmul (pEmulDV n p)).

    eapply valrel_lambda; crush.

    intros w' vs vu futw valrel.

    fold apTm apUTm.
    crushUtlcSyntaxMatchH; crushStlcSyntaxMatchH.
    rewrite ?ap_comp.

    assert (lev w' ≤ m) by (unfold lev in *; Omega.omega).

    eapply tr;
      eauto using extend_envrel, envrel_mono.
Qed.

Lemma compat_emul_pabs {n m d p Γ} :
  dir_world_prec n m d p →
  ⟪ ⊩ S.pctx_cat (S.pabs (UVal n) S.phole) (inArrDwn_pctx n) ⟦ d , m ⟧ U.pabs U.phole : Γ p▻ pEmulDV n p , pEmulDV n p → Γ , pEmulDV n p ⟫.
Proof.
  intros dwp.
  split.
  - eauto using inArrDwn_pctx_T with typing uval_typing.
  - intros ts tu lr.
    change (S.pctx_app ts (S.pctx_cat (S.pabs (UVal n) S.phole) (inArrDwn_pctx n)))
    with (inArrDwn n (S.abs (UVal n) ts)).
    eauto using compat_emul_abs.
Qed.

Lemma termrel_caseArrUp {d w n p ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts₁ tu₁ →
  (∀ w' : World, w' ≤ w → termrel d w' (pEmulDV n p) ts₂ tu₂) →
  termrel d w (pEmulDV n p) 
          (S.app (S.app (S.abs (UVal n) (S.abs (UVal n) (S.app (caseArrUp n (S.var 1)) (S.var 0)))) ts₁) ts₂) (U.app tu₁ tu₂).
Proof.
  intros dwp tr₁ tr₂.
  unfold caseArrUp, caseArrUp_pctx.
  (* evaluate ts₁ and tu₁ *)
  eapply (termrel_ectx' tr₁); S.inferContext; U.inferContext; 
  unfold pctx_cat, U.ECtx; crush.

  (* continuation boilerplate *)
  intros w' futw vs₁ vu₁ vr₁.
  destruct (valrel_implies_OfType vr₁) as [[vvs₁ ?] ?].
  rewrite pctx_cat_app; cbn.

  (* beta-reduce the outer let *)
  eapply termrel_antired_eval_left.
  eapply (eval_from_eval₀ (eval_beta vvs₁)); S.inferContext; crush.
  cbn; crush.

  (* bureaucracy *)
  fold (caseArr n (S.app (upgrade n 1) (S.var 1))).
  rewrite caseArr_sub; cbn; crush; rewrite upgrade_sub.

  (* evaluate ts₂ and tu₂ *)
  specialize (tr₂ w' futw).
  eapply (termrel_ectx' tr₂); S.inferContext; U.inferContext; 
  unfold pctx_cat, U.ECtx; crush.
  
  (* continuation boilerplate *)
  intros w'' futw' vs₂ vu₂ vr₂.
  destruct (valrel_implies_Value vr₂) as [vvs₂ ?].
  cbn.

  (* beta-reduce the remaining let *)
  eapply termrel_antired_eval_left.
  eapply (eval_from_eval₀ (eval_beta vvs₂)); S.inferContext; crush.
  cbn; crush.

  (* bureaucracy *)
  fold (caseArr n (S.app (upgrade n 1) (S.var 1))).
  rewrite ?caseArr_sub; cbn; crush; rewrite ?upgrade_sub.
  rewrite <- ?ap_liftSub; rewrite -> ?liftSub_wkm; rewrite (apply_wkm_beta1_cancel vs₁ vs₂).
  
  (* execute the upgrade *)
  assert (w'' ≤ w) by Omega.omega.
  assert (valrel d w'' (pEmulDV n p) vs₁ vu₁) by eauto using valrel_mono.
  assert (trupg : termrel d w'' (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs₁) vu₁)
    by (eauto using upgrade_works', dwp_mono).
  unfold caseArr.
  eapply (termrel_ectx' trupg); S.inferContext; U.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros w''' futw'' vs₁' vu₁' vr₁'.
  replace (n + 1) with (S n) in vr₁' by Omega.omega.

  destruct (valrel_implies_Value vr₁').
  (* case analysis *)
  eapply invert_valrel_pEmulDV_for_caseUValArr in vr₁'.
  destruct vr₁' as [(vs₁'' & ? & es & vr₁')|[(? & div)|(neq & div)]]; subst.
  - (* Correct case *)

    (* caseArr succeeds *)
    eapply termrel_antired_star_left.
    fold (caseArr n (inArr n vs₁'')).
    eapply (evalstar_ctx' es); S.inferContext; crush.
    cbn.

    (* application works *)
    eapply valrel_in_termrel in vr₁'.
    eapply (termrel_app vr₁').

    (* application argument is also fine *)
    eauto using valrel_in_termrel, valrel_mono.
  - (* unk case *) 
    eapply dwp_imprecise in dwp; subst.
    eapply termrel_div_lt.
    fold (caseArr n vs₁').
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - (* other cases *)
    
    eapply termrel_div_wrong.
    + fold (caseArr n vs₁').
      eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      eapply evalToStar.
      eapply U.eval₀_to_eval.
      eauto with eval.
Qed.


Lemma compat_emul_app {n m d p Γ ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ S.app (S.app (S.abs (UVal n) (S.abs (UVal n) (S.app (caseArrUp n (S.var 1)) (S.var 0)))) ts₁) ts₂ ⟦ d , m ⟧ U.app tu₁ tu₂ : pEmulDV n p ⟫.
Proof.
  intros dwp [ty₁ tr₁] [ty₂ tr₂].
  split.
  - eauto using caseArrUp_T with typing uval_typing.
  - intros w wn γs γu envrel.
    unfold lev in *.

    specialize (tr₁ w wn γs γu envrel).
    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    change (S.app (caseArrUp n ts₁) ts₂)[γs] 
    with (S.app (caseArrUp n ts₁) [γs] ts₂[γs]).
    change (U.app tu₁ tu₂)[γu] with (U.app tu₁[γu] tu₂[γu]).
    cbn; crush.
    rewrite caseArrUp_sub; cbn; crush.
    change (wk 0) with 1.

    eapply termrel_caseArrUp; eauto.
    intros w' futw.
    eauto using envrel_mono with arith.
Qed.