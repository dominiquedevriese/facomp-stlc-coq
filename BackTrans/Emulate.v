Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import BackTrans.UValHelpers.
Require Import BackTrans.UValHelpers2.
Require Import Stlc.SpecTyping.
Require Import Stlc.StlcOmega.
Require Import Stlc.LemmasTyping.
Require Import Stlc.SpecEvaluation.
Require Import Stlc.LemmasEvaluation.
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
Require Import UVal.UVal.
Require Utlc.Fix.
Require Omega.

Fixpoint emulate (n : nat) (t : U.UTm) : S.Tm :=
  match t with
    | U.wrong => stlcOmega (UVal n)
    | U.var i => S.var i
    | U.abs t => inArrDwn n (S.abs (UVal n) (emulate n t))
    | U.app t₁ t₂ => uvalApp n (emulate n t₁) (emulate n t₂)
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
    | U.papp₁ C t₂ => S.pctx_cat (emulate_pctx n C) (uvalApp_pctx₁ n (emulate n t₂))
    | U.papp₂ t₁ C => S.pctx_cat (emulate_pctx n C) (uvalApp_pctx₂ n (emulate n t₁)) 
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
  eauto using toUVals_entry with typing uval_typing.
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
          repeat crushUtlcEvaluationMatchH; 
          repeat crushUtlcEvaluationMatchH2; 
          repeat crushUtlcEvaluationMatchH2; 
          repeat crushUtlcScopingMatchH;
          repeat crushDbSyntaxMatchH;
          repeat crushDbLemmasMatchH;
          repeat crushDbLemmasRewriteH;
          try assumption;
          crushOfType;
          trivial;
          eauto using caseUnit_pctx_ECtx, caseBool_pctx_ECtx, caseProd_pctx_ECtx, caseSum_pctx_ECtx, caseArr_pctx_ECtx, upgrade_value, downgrade_value with typing
         ).

Lemma termrel_omega_wrong { d w pτ} :
  termrel d w pτ (stlcOmega (repEmul pτ)) wrong.
Proof.
  eauto using termrel_div_wrong, stlcOmega_div with eval.
Qed.

Lemma compat_emul_wrong {Γ pτ d m} :
  ⟪ Γ ⊩ stlcOmega (repEmul pτ) ⟦ d , m ⟧ wrong : pτ ⟫.
Proof.
  split; [|split]; crush.
  intros w wn γs γu envrel.
  rewrite stlcOmega_sub.
  eauto using termrel_omega_wrong.
Qed.

Lemma compat_emul_wrong' {Γ n p d m} :
  ⟪ Γ ⊩ stlcOmega (UVal n) ⟦ d , m ⟧ wrong : pEmulDV n p ⟫.
Proof.
  change (UVal n) with (repEmul (pEmulDV n p)).
  eauto using compat_emul_wrong. 
Qed.

Lemma compat_emul_unit {Γ d n p m} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ inUnitDwn n S.unit ⟦ d , m ⟧ U.unit : pEmulDV n p ⟫.
Proof.
  intros dwp.
  split; [|split]. 
  - eauto using inUnitDwn_T with typing uval_typing.
  - crush.
  - intros w wn γs γu envrel.
    rewrite inUnitDwn_sub.
    simpl.
    eapply termrel₀_in_termrel.
    eauto using termrel₀_inUnitDwn, dwp_mono, valrel_in_termrel, valrel_unit with arith.
Qed.

Lemma compat_emul_true {Γ d n p m} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ inBoolDwn n S.true ⟦ d , m ⟧ U.true : pEmulDV n p ⟫.
Proof.
  intros dwp.
  split; [|split].
  - eauto using inBoolDwn_T with typing uval_typing.
  - crush.
  - intros w wn γs γu envrel.
    rewrite inBoolDwn_sub.
    simpl.
    eapply termrel₀_in_termrel.
    eauto using termrel₀_inBoolDwn, dwp_mono, valrel_in_termrel, valrel_true with arith.
Qed.

Lemma compat_emul_false {Γ d n p m} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ inBoolDwn n S.false ⟦ d , m ⟧ U.false : pEmulDV n p ⟫.
Proof.
  intros dwp.
  split; [|split].
  - eauto using inBoolDwn_T with typing uval_typing.
  - crush.
  - intros w wn γs γu envrel.
    rewrite inBoolDwn_sub.
    simpl.
    eapply termrel₀_in_termrel.
    eauto using termrel₀_inBoolDwn, dwp_mono, valrel_in_termrel, valrel_false with arith.
Qed.

Lemma compat_emul_abs {n m d p Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ p▻ pEmulDV n p ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ inArrDwn n (S.abs (UVal n) ts) ⟦ d , m ⟧ U.abs tu : pEmulDV n p ⟫.
Proof.
  intros dwp [ty [closed tr]].
  split; [|split].
  - eauto using inArrDwn_T with typing uval_typing.
  - crush.
  - intros w wn γs γu envrel.

    assert (OfType (ptarr (pEmulDV n p) (pEmulDV n p))
                   (S.abs (repEmul (pEmulDV n p)) 
                          (ts [γs↑])) (U.abs (tu [γu↑])))
      by (pose proof (envrel_implies_WtSub envrel);
          pose proof (envrel_implies_WsSub envrel);
          crush).

    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    rewrite inArrDwn_sub.
    eapply termrel₀_in_termrel.
    eapply termrel₀_inArrDwn; try assumption.

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

(* Lemma compat_emul_pabs {n m d p Γ} : *)
(*   dir_world_prec n m d p → *)
(*   ⟪ ⊩ S.pctx_cat (S.pabs (UVal n) S.phole) (inArrDwn_pctx n) ⟦ d , m ⟧ U.pabs U.phole : Γ p▻ pEmulDV n p , pEmulDV n p → Γ , pEmulDV n p ⟫. *)
(* Proof. *)
(*   intros dwp. *)
(*   split. *)
(*   - eauto using inArrDwn_pctx_T with typing uval_typing. *)
(*   - intros ts tu lr. *)
(*     change (S.pctx_app ts (S.pctx_cat (S.pabs (UVal n) S.phole) (inArrDwn_pctx n))) *)
(*     with (inArrDwn n (S.abs (UVal n) ts)). *)
(*     eauto using compat_emul_abs. *)
(* Qed. *)

Lemma compat_emul_pair {n m d p Γ ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ inProdDwn n (S.pair ts₁ ts₂) ⟦ d , m ⟧ U.pair tu₁ tu₂ : pEmulDV n p ⟫.
Proof.
  intros dwp tr₁ tr₂.
  destruct tr₁ as (? & ? & tr₁).
  destruct tr₂ as (? & ? & tr₂).
  split; [|split].
  - eauto using inProdDwn_T with typing uval_typing.
  - crushUtlcScoping.
  - intros w wm γs γu envrel.
    rewrite inProdDwn_sub.
    enough (termrel d w (ptprod (pEmulDV n p) (pEmulDV n p)) (S.pair ts₁ ts₂)[γs] (U.pair tu₁ tu₂)[γu]) as trp.
    + eapply (termrel_ectx' trp); S.inferContext; U.inferContext; simpl; crush.
      intros w' futw vs vu vr.
      eapply termrel₀_in_termrel.
      eapply termrel₀_inProdDwn;
        eauto using dwp_mono with arith.
    + eapply termrel_pair;
      fold apTm apUTm; crush.
      intros w' fw; eapply tr₂; eauto using envrel_mono with arith.
Qed.

Lemma termrel_emul_caseof {n w d p ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts₁ tu₁ →
  (forall w' vs₂ vu₂, w' ≤ w →
                      valrel d w' (pEmulDV n p) vs₂ vu₂ →
                      termrel d w' (pEmulDV n p) (ts₂ [beta1 vs₂]) (tu₂ [beta1 vu₂])) →
  (forall w' vs₃ vu₃, w' ≤ w →
                      valrel d w' (pEmulDV n p) vs₃ vu₃ →
                      termrel d w' (pEmulDV n p) (ts₃ [beta1 vs₃]) (tu₃ [beta1 vu₃])) →
  termrel d w (pEmulDV n p) (S.caseof (caseSumUp n ts₁) ts₂ ts₃) (U.caseof tu₁ tu₂ tu₃).
Proof.
  intros dwp tr₁ tr₂ tr₃. 
  unfold caseSumUp.
  (* evaluate ts₁ and ts₂ *)
  eapply (termrel_ectx' tr₁); S.inferContext; U.inferContext; crush;
  eauto using caseSumUp_pctx_ectx.

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseSumUp_pctx; rewrite S.pctx_cat_app; crush; cbn.

  (* evaluate upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel_ectx' trupg); S.inferContext; U.inferContext; crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  fold (caseSum n vs'); cbn.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValSum in vr'.
  destruct vr' as [(vs₁' & ? & es & vr₁')|
                   [(? & div)| (neql & neqr & div)]]; subst.

  - (* successful caseUValBool *)
    eapply termrel_antired_star_left.
    eapply (evalstar_ctx' es); S.inferContext; crush.

    cbn.
    eapply termrel_caseof; eauto using valrel_in_termrel.
    + intros w''' vs₂' vu₂' fw'' vr₂. eapply tr₂; eauto with arith.
    + intros w''' vs₃' vu₃' fw'' vr₃. eapply tr₃; eauto with arith.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - (* other cases *)
    eapply termrel_div_wrong.
    + eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      eapply evalToStar.
      eapply eval₀_to_eval.
      eauto with eval.
Qed.

Lemma compat_emul_caseof {n m d p Γ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p ⟫ →
  ⟪ Γ p▻ pEmulDV n p ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p ⟫ →
  ⟪ Γ p▻ pEmulDV n p ⊩ ts₃ ⟦ d , m ⟧ tu₃ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ S.caseof (caseSumUp n ts₁) ts₂ ts₃ ⟦ d , m ⟧ U.caseof tu₁ tu₂ tu₃ : pEmulDV n p ⟫.
Proof.
  intros dwp lr₁ lr₂ lr₃.
  destruct lr₁ as (? & ? & tr₁).
  destruct lr₂ as (? & ? & tr₂).
  destruct lr₃ as (? & ? & tr₃).
  split; [|split].
  - eauto with typing uval_typing.
  - crushUtlcScoping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseSumUp_sub.
    eapply termrel_emul_caseof; 
      eauto using envrel_mono, dwp_mono with arith;
      intros w' vs₂ vu₂ fw vr₂;
      rewrite ?ap_comp;
      assert (lev w' ≤ m) by (unfold lev in *; Omega.omega);
      [eapply tr₂|eapply tr₃]; 
      eauto using extend_envrel, envrel_mono.
Qed. 
      
Lemma termrel_emul_ite {n w d p ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts₁ tu₁ →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p) ts₂ tu₂) →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p) ts₃ tu₃) →
  termrel d w (pEmulDV n p) (S.ite (caseBoolUp n ts₁) ts₂ ts₃) (U.ite tu₁ tu₂ tu₃).
Proof.
  intros dwp tr₁ tr₂ tr₃. 
  unfold caseBoolUp.
  (* evaluate ts₁ and ts₂ *)
  eapply (termrel_ectx' tr₁); S.inferContext; U.inferContext; crush;
  eauto using caseBoolUp_pctx_ectx.

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseBoolUp_pctx; rewrite S.pctx_cat_app; cbn.

  (* evaluate upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel_ectx' trupg); S.inferContext; U.inferContext; crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  fold (caseBool vs'); cbn.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValBool in vr'.
  destruct vr' as [(vs₁' & ? & es & vr₁')|
                   [(? & div)| (neqt & neqf & div)]]; subst.

  - (* successful caseUValBool *)
    eapply termrel_antired_star_left.
    eapply (evalstar_ctx' es); S.inferContext; crush.

    cbn.
    eapply termrel_ite; eauto using valrel_in_termrel.
    + intros w''' fw''. eapply tr₂; Omega.omega.
    + intros w''' fw''. eapply tr₃; Omega.omega.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - (* other cases *)
    eapply termrel_div_wrong.
    + eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      eapply evalToStar.
      eapply eval₀_to_eval.
      eauto with eval.
Qed.

Lemma compat_emul_ite {n m d p Γ ts₁ tu₁ ts₂ tu₂ ts₃ tu₃} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ ts₃ ⟦ d , m ⟧ tu₃ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ S.ite (caseBoolUp n ts₁) ts₂ ts₃ ⟦ d , m ⟧ U.ite tu₁ tu₂ tu₃ : pEmulDV n p ⟫.
Proof.
  intros dwp lr₁ lr₂ lr₃.
  destruct lr₁ as (? & ? & tr₁).
  destruct lr₂ as (? & ? & tr₂).
  destruct lr₃ as (? & ? & tr₃).
  split; [|split].
  - simpl in *.
    eauto with typing uval_typing.
  - crushUtlcScoping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseBoolUp_sub.
    eapply termrel_emul_ite; eauto using envrel_mono, dwp_mono with arith.
Qed. 
      
Lemma compat_emul_app {n m d p Γ ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ uvalApp n ts₁ ts₂ ⟦ d , m ⟧ U.app tu₁ tu₂ : pEmulDV n p ⟫.
Proof.
  intros dwp (? & ? & tr₁) (? & ? & tr₂).
  split; [|split].
  - unfold uvalApp.
    eauto using caseArrUp_T with typing uval_typing.
  - crushUtlcScoping.
  - intros w wn γs γu envrel.
    unfold lev in *.

    specialize (tr₁ w wn γs γu envrel).
    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    change (S.app (caseArrUp n ts₁) ts₂)[γs] 
    with (S.app (caseArrUp n ts₁) [γs] ts₂[γs]).
    change (U.app tu₁ tu₂)[γu] with (U.app tu₁[γu] tu₂[γu]).
    cbn; crush.
    rewrite uvalApp_sub; cbn; crush.
    change (wk 0) with 1.

    eapply termrel_uvalApp; eauto.
    intros w' futw.
    eauto using envrel_mono with arith.
Qed.

Lemma termrel_emul_seq {n w d p ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts₁ tu₁ →
  (forall w', w' ≤ w → termrel d w' (pEmulDV n p) ts₂ tu₂) →
  termrel d w (pEmulDV n p) (S.seq (caseUnitUp n ts₁) ts₂) (U.seq tu₁ tu₂).
Proof.
  intros dwp tr₁ tr₂.
  unfold caseUnitUp.

  (* evaluate ts₁ and tu₁ *)
  eapply (termrel_ectx' tr₁); S.inferContext; U.inferContext; cbn; eauto using caseUnitUp_pctx_ectx. 

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.

  (* do the upgrade *)
  unfold caseUnitUp_pctx; rewrite S.pctx_cat_app; cbn.
  assert (trupg : termrel d w' (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel_ectx' trupg); S.inferContext; U.inferContext; cbn; crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.

  (* case analysis *)
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValUnit in vr'.
  fold (caseUnit vs').
  destruct vr' as [(? & ? & es)|
                   [(? & div)|(? & div)]]; subst.
  - (* successful caseUValUnit *)
    eapply termrel_antired_star_left.
    eapply (evalstar_ctx' es); S.inferContext; crush.

    subst; cbn.
    eapply termrel_seq.
    + eauto using valrel_in_termrel, valrel_unit.
    + intros; eapply tr₂; eauto with arith.
  - (* unk case *)
    eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - (* other cases *)
    eapply termrel_div_wrong.
    + eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      eapply evalToStar.
      eapply eval₀_to_eval.
      eauto with eval.
Qed.
  
Lemma compat_emul_seq {n m d p Γ ts₁ tu₁ ts₂ tu₂} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts₁ ⟦ d , m ⟧ tu₁ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ ts₂ ⟦ d , m ⟧ tu₂ : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ S.seq (caseUnitUp n ts₁) ts₂ ⟦ d , m ⟧ U.seq tu₁ tu₂ : pEmulDV n p ⟫.
Proof.
  intros dwp (? & ? & tr₁) (? & ? & tr₂).
  split; [|split].
  - eauto using caseUnitUp_T with typing uval_typing.
  - crushUtlcScoping.
  - intros w wn γs γu envrel.

    specialize (tr₁ w wn γs γu envrel).
    assert (dir_world_prec n w d p) by eauto using dwp_mono.

    cbn; crush.
    rewrite caseUnitUp_sub.

    eapply termrel_emul_seq; eauto.
    intros w' fw; eapply tr₂; eauto using envrel_mono with arith.
Qed.

Lemma termrel_emul_inl {n w d p ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts tu →
  termrel d w (pEmulDV n p) (inSumDwn n (S.inl ts)) (U.inl tu).
Proof.
  intros dwp tr.
  unfold inSumDwn.
  eapply (termrel_ectx' tr); S.inferContext; U.inferContext; crush;
  eauto using inSumDwn_pctx_ectx. 
  intros w' fw vs vu vr.
  eapply termrel₀_in_termrel.
  eapply termrel₀_inSumDwn; simpl; eauto using valrel_inl, dwp_mono.
Qed.

Lemma compat_emul_inl {n m d p Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ inSumDwn n (S.inl ts) ⟦ d , m ⟧ U.inl tu : pEmulDV n p ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crushUtlcScoping.
  - intros w wm γs γu envrel.
    rewrite inSumDwn_sub.
    eapply termrel_emul_inl; eauto using dwp_mono.
Qed.
    
Lemma termrel_emul_inr {n w d p ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts tu →
  termrel d w (pEmulDV n p) (inSumDwn n (S.inr ts)) (U.inr tu).
Proof.
  intros dwp tr. unfold inSumDwn.
  eapply (termrel_ectx' tr); S.inferContext; U.inferContext; crush;  
  eauto using inSumDwn_pctx_ectx. 
  intros w' fw vs vu vr.
  eapply termrel₀_in_termrel.
  eapply termrel₀_inSumDwn; simpl; eauto using valrel_inr, dwp_mono.
Qed.

Lemma compat_emul_inr {n m d p Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ inSumDwn n (S.inr ts) ⟦ d , m ⟧ U.inr tu : pEmulDV n p ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crushUtlcScoping.
  - intros w wm γs γu envrel.
    rewrite inSumDwn_sub.
    eapply termrel_emul_inr; eauto using dwp_mono.
Qed.
    
Lemma termrel_emul_proj₁ {n w d p ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts tu →
  termrel d w (pEmulDV n p) (S.proj₁ (caseProdUp n ts)) (U.proj₁ tu).
Proof.
  intros dwp tr.
  unfold caseProdUp.

  (* evaluate ts and tu *)
  eapply (termrel_ectx' tr); S.inferContext; U.inferContext; crush; 
  eauto using caseProdUp_pctx_ectx.

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseProdUp_pctx; rewrite S.pctx_cat_app; cbn.

  (* execute the upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel_ectx' trupg); S.inferContext; U.inferContext; crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValProd in vr'.
  fold (caseProd n vs').
  destruct vr' as [(vs'' & ? & es & vr'')|
                   [(? & div)|(? & div)]].
  - eapply termrel_antired_star_left.
    eapply (evalstar_ctx' es); S.inferContext; crush.
    simpl.
    eauto using termrel_proj₁, valrel_in_termrel.
  - subst; eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - eapply termrel_div_wrong.
    + eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      simpl.
      eapply evalToStar.
      eapply eval₀_to_eval.
      eauto with eval.
Qed.    

Lemma compat_emul_proj₁ {n m d p Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ S.proj₁ (caseProdUp n ts) ⟦ d , m ⟧ U.proj₁ tu : pEmulDV n p ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crushUtlcScoping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseProdUp_sub.
    eapply termrel_emul_proj₁; eauto using dwp_mono.
Qed.

Lemma termrel_emul_proj₂ {n w d p ts tu} :
  dir_world_prec n w d p →
  termrel d w (pEmulDV n p) ts tu →
  termrel d w (pEmulDV n p) (S.proj₂ (caseProdUp n ts)) (U.proj₂ tu).
Proof.
  intros dwp tr.
  unfold caseProdUp.

  (* evaluate ts and tu *)
  eapply (termrel_ectx' tr); S.inferContext; U.inferContext; crush; 
  eauto using caseProdUp_pctx_ectx.

  (* continuation bureaucracy *)
  intros w' fw vs vu vr.
  unfold caseProdUp_pctx; rewrite S.pctx_cat_app; cbn.

  (* execute the upgrade *)
  assert (trupg : termrel d w' (pEmulDV (n + 1) p) (S.app (upgrade n 1) vs) vu)
    by eauto using upgrade_works', dwp_mono.
  replace (n + 1) with (S n) in trupg by Omega.omega.
  eapply (termrel_ectx' trupg); S.inferContext; U.inferContext; crush.

  (* continuation bureaucracy *)
  intros w'' fw' vs' vu' vr'.
  destruct (valrel_implies_Value vr').
  eapply invert_valrel_pEmulDV_for_caseUValProd in vr'.
  fold (caseProd n vs').
  destruct vr' as [(vs'' & ? & es & vr'')|
                   [(? & div)|(? & div)]].
  - eapply termrel_antired_star_left.
    eapply (evalstar_ctx' es); S.inferContext; crush.
    simpl.
    eauto using termrel_proj₂, valrel_in_termrel.
  - subst; eapply dwp_invert_imprecise in dwp; subst.
    eapply termrel_div_lt.
    eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
  - eapply termrel_div_wrong.
    + eapply (divergence_closed_under_evalcontext' div); S.inferContext; crush.
    + right.
      simpl.
      eapply evalToStar.
      eapply eval₀_to_eval.
      eauto with eval.
Qed.

Lemma compat_emul_proj₂ {n m d p Γ ts tu} :
  dir_world_prec n m d p →
  ⟪ Γ ⊩ ts ⟦ d , m ⟧ tu : pEmulDV n p ⟫ →
  ⟪ Γ ⊩ S.proj₂ (caseProdUp n ts) ⟦ d , m ⟧ U.proj₂ tu : pEmulDV n p ⟫.
Proof.
  intros dwp lr.
  destruct lr as (? & ? & tr).
  split; [|split].
  - simpl in *.
    eauto using inSumDwn_T with typing uval_typing.
  - crushUtlcScoping.
  - intros w wm γs γu envrel.
    cbn; crush.
    rewrite caseProdUp_sub.
    eapply termrel_emul_proj₂; eauto using dwp_mono.
Qed.
    
Fixpoint toEmulDV n p (Γ : Dom) : PEnv :=
  match Γ with
      0 => pempty
    | S Γ' => toEmulDV n p Γ' p▻ pEmulDV n p
  end.

Lemma toEmulDV_entry {n p Γ i} :
  Γ ∋ i → ⟪ i : pEmulDV n p p∈ toEmulDV n p Γ ⟫.
Proof.
  induction 1; simpl; eauto using GetEvarP.
Qed.

Lemma toEmulDV_repEmulCtx {n p Γ} :
  repEmulCtx (toEmulDV n p Γ) = toUVals n Γ.
Proof.
  induction Γ; cbn; f_equal; trivial.
Qed.

Lemma emulate_works { Γ tu n p d m} :
  dir_world_prec n m d p →
  ⟨ Γ ⊢ tu ⟩ →
  ⟪ toEmulDV n p Γ ⊩ emulate n tu ⟦ d , m ⟧ tu : pEmulDV n p ⟫.
Proof.
  intros dwp; induction 1; 
  eauto using compat_emul_app, compat_emul_abs, compat_var, toEmulDV_entry, compat_emul_wrong', compat_emul_unit, compat_emul_true, compat_emul_false, compat_emul_pair, compat_emul_ite, compat_emul_inl, compat_emul_inr, compat_emul_proj₁, compat_emul_proj₂, compat_emul_seq, compat_emul_caseof.
Qed.


Lemma emulate_pctx_works { Γ Γ' Cu n p d m} :
  dir_world_prec n m d p →
  ⟨ ⊢ Cu : Γ → Γ' ⟩ →
  ⟪ ⊩ emulate_pctx n Cu ⟦ d , m ⟧ Cu : toEmulDV n p Γ , pEmulDV n p → toEmulDV n p Γ' , pEmulDV n p ⟫.
Proof.
  intros dwp scp; unfold OpenLRCtxN; split.
  - simpl; rewrite ?toEmulDV_repEmulCtx.
    eauto using emulate_pctx_T.  
  - induction scp; cbn;
    intros ts tu lr; 
    rewrite ?S.pctx_cat_app, ?uvalApp_pctx₁_app, ?uvalApp_pctx₂_app;
    eauto using emulate_works, compat_emul_app, compat_emul_abs, compat_var, toEmulDV_entry, compat_emul_wrong', compat_emul_unit, compat_emul_true, compat_emul_false, compat_emul_pair, compat_emul_ite, compat_emul_inl, compat_emul_inr, compat_emul_proj₁, compat_emul_proj₂, compat_emul_seq, compat_emul_caseof;
    eapply compat_emul_caseof; crush;
    change (toEmulDV n p γ p▻ pEmulDV n p) with (toEmulDV n p (S γ));
    eauto using emulate_works.
Qed.