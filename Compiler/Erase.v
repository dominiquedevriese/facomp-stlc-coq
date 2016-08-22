Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Stlc.LemmasEvaluation.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import LogRel.PseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import Omega.
Require Import Db.Lemmas.
Require Utlc.Fix.

Module S.
    Include Stlc.SpecSyntax.
    Include Stlc.LemmasEvaluation.
    Include Stlc.LemmasTyping.
End S.
Module U.
  Include Utlc.SpecSyntax.
  Include Utlc.Fix.
End U.

Fixpoint erase (t : S.Tm) : U.UTm :=
  match t with
    | S.abs τ t         => U.abs (erase t)
    | S.unit            => U.unit
    | S.true            => U.true
    | S.false           => U.false
    | S.pair t₁ t₂      => U.pair (erase t₁) (erase t₂)
    | S.inl t           => U.inl (erase t)
    | S.inr t           => U.inr (erase t)
    | S.var x           => U.var x
    | S.app t₁ t₂       => U.app (erase t₁) (erase t₂)
    | S.ite t₁ t₂ t₃    => U.ite (erase t₁) (erase t₂) (erase t₃)
    | S.proj₁ t₁        => U.proj₁ (erase t₁)
    | S.proj₂ t₁        => U.proj₂ (erase t₁)
    | S.caseof t₁ t₂ t₃ => U.caseof (erase t₁) (erase t₂) (erase t₃)
    | S.seq t₁ t₂       => U.seq (erase t₁) (erase t₂)
    | S.fixt _ _ t₁     => U.app U.ufix (erase t₁)
  end.

Fixpoint erase_pctx (C : S.PCtx) : U.PCtx :=
  match C with
    | S.phole => phole
    | S.pabs τ C => U.pabs (erase_pctx C)
    | S.papp₁ C t => U.papp₁ (erase_pctx C) (erase t) 
    | S.papp₂ t C => U.papp₂ (erase t) (erase_pctx C)
    | S.pite₁ C t₂ t₃ => U.pite₁ (erase_pctx C) (erase t₂) (erase t₃)
    | S.pite₂ t₁ C t₃ => U.pite₂ (erase t₁) (erase_pctx C) (erase t₃)
    | S.pite₃ t₁ t₂ C => U.pite₃ (erase t₁) (erase t₂) (erase_pctx C)
    | S.ppair₁ C t => U.ppair₁ (erase_pctx C) (erase t)
    | S.ppair₂ t C => U.ppair₂ (erase t) (erase_pctx C)
    | S.pproj₁ C => U.pproj₁ (erase_pctx C)
    | S.pproj₂ C => U.pproj₂ (erase_pctx C)
    | S.pinl C => U.pinl (erase_pctx C)
    | S.pinr C => U.pinr (erase_pctx C)
    | S.pcaseof₁ C t₂ t₃ => U.pcaseof₁ (erase_pctx C) (erase t₂) (erase t₃)
    | S.pcaseof₂ t₁ C t₃ => U.pcaseof₂ (erase t₁) (erase_pctx C) (erase t₃)
    | S.pcaseof₃ t₁ t₂ C => U.pcaseof₃ (erase t₁) (erase t₂) (erase_pctx C)
    | S.pseq₁ C t => U.pseq₁ (erase_pctx C) (erase t)
    | S.pseq₂ t C => U.pseq₂ (erase t) (erase_pctx C)
    | S.pfixt τ₁ τ₂ C => U.papp₂ U.ufix (erase_pctx C)
  end.

Lemma erase_scope (t : S.Tm) (Γ : S.Env) (τ : S.Ty) :
  ⟪ Γ ⊢ t : τ ⟫ -> ⟨ dom Γ ⊢ erase t ⟩.
Proof.
  intro wt; induction wt; crushUtlcScoping.
  apply U.ufix_ws.
Qed.

Hint Extern 4 ⟨ _ ⊢ erase ?t ⟩ =>
  match goal with
      [ H : ⟪ _ ⊢ ?t : _ ⟫ |- _ ] => refine (erase_scope _ _ _ H)
  end.

Lemma erase_pctx_scope (C : S.PCtx) (Γ₀ Γ : S.Env) (τ₀ τ : S.Ty) :
  ⟪ ⊢ C : Γ₀ , τ₀ → Γ , τ ⟫ → ⟨ ⊢ erase_pctx C : dom Γ₀ → dom Γ ⟩.
Proof.
  intro wt; induction wt; crushUtlcScoping.
  apply U.ufix_ws.
Qed.

Local Ltac crush :=
  repeat (repeat match goal with
                  [ |- _ ∧ _ ] => split
                | [ |- ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ ] => (unfold OpenLRN; split)
                | [ H : ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ |- _ ] => (unfold OpenLRN in H; destruct_conjs)
                | [ |- termrel _ _ _ (S.abs _ _) (U.abs _) ] => apply valrel_in_termrel
                | [ |- termrel _ _ _ S.unit U.unit ] => apply valrel_in_termrel
                | [ |- termrel _ _ _ S.false U.false ] => apply valrel_in_termrel
                | [ |- termrel _ _ _ S.true U.true ] => apply valrel_in_termrel
                | [ H : valrel ?d ?w ?τ ?ts ?tu |- valrel ?d ?w' ?τ ?ts ?tu ] => refine (valrel_mono _ H); try omega
                | [ |- valrel _ _ _ _ _] => rewrite -> valrel_fixp in |- *; unfold valrel' in |- *
                | [ |- exists tsb tub, S.abs _ ?tsb' = S.abs _ tsb ∧ U.abs ?tub' = U.abs tub ∧ _] => exists tsb'; exists tub'; split; intuition
                | [ |- exists t', U.abs ?t = U.abs t' ] => exists t; intuition
                | [ |- S.ECtx (S.pctx_cat _ _) ] => apply S.ectx_cat
                | [ |- U.ECtx (U.pctx_cat _ _) ] => apply U.ectx_cat
                | [ H: exists tub', ?tu = U.abs tub' |- U.Value ?tu ] => destruct H as [? ?]; subst
                | [ |- exists ts₁' ts₂' tu₁' tu₂', S.pair ?ts₁ ?ts₂ = S.pair ts₁' ts₂' ∧ U.pair ?tu₁ ?tu₂ = LR.U.pair tu₁' tu₂' ∧ _ ] => exists ts₁; exists ts₂; exists tu₁; exists tu₂
                | [ |- (exists ts₁' tu₁', S.inl ?ts₁ = LR.S.inl ts₁' ∧ U.inl ?tu₁ = LR.U.inl tu₁' ∧ _) ∨ _ ] => left; exists ts₁; exists tu₁
                | [ |- _ ∨ (exists ts₁' tu₁', S.inr ?ts₁ = LR.S.inr ts₁' ∧ U.inr ?tu₁ = LR.U.inr tu₁' ∧ _) ] => right; exists ts₁; exists tu₁
                | [ |- sum_rel _ _ _ _ ] => unfold sum_rel
                | [ |- prod_rel _ _ _ _ ] => unfold prod_rel
              end;
          crushTyping;
          intuition);
  repeat match goal with
           | [ H : valrel' ?d ?w _ ?τ ?ts ?tu |- _ ] => change _ with (valrel d w τ ts tu) in H
           | [ |- valrel' ?d ?w _ ?τ ?ts ?tu ] => change _ with (valrel d w τ ts tu)
           | [ H : valrel ?d ?w ?τ ?ts ?tu |- valrel ?d ?w' ?τ ?ts ?tu ] => refine (valrel_mono _ H); try omega
           | [ H : valrel _ _ ?τ ?ts ?tu |- OfType ?τ ?ts ?tu ] => refine (valrel_implies_OfType H)
         end.

Section CompatibilityLemmas.
  Lemma compat_lambda {Γ τ' ts d n tu τ} :
    ⟪ Γ p▻ τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (S.abs (repEmul τ') ts) ⟦ d , n ⟧ abs tu : ptarr τ' τ ⟫.
  Proof.
    intros lr. crush.
    - (* OfType *)
      unfold OfType, OfTypeStlc, OfTypeUtlc; repeat split.
      + (* OfTypeStlc *)
        change (S.abs (repEmul τ') (ts [γs↑])) with ((S.abs (repEmul τ') ts) [γs]).
        refine (S.typing_sub _ _ _ _); crushTyping.
        refine (envrel_implies_WtSub H2).
      + (* OfTypeUtlc *)
        crush.
    - (* valrel_ptarr hypothesis *)
      rewrite -> (ap_comp ts (γs↑) (beta1 ts')).
      change (apUTm γu↑ tu) with (tu [γu↑]).
      rewrite -> (ap_comp tu (γu↑) (beta1 tu')).
      refine (H0 w' _ (γs↑ >=> beta1 ts') (γu↑ >=> beta1 tu') _).
      + unfold lev in *. omega.
      + eauto using extend_envrel, envrel_mono.
  Qed.

  Lemma compat_lambda_embed {Γ τ' ts d n tu τ} :
    ⟪ Γ p▻ embed τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ →
    ⟪ Γ ⊩ (S.abs τ' ts) ⟦ d , n ⟧ abs tu : ptarr (embed τ') τ ⟫.
  Proof.
    rewrite <- (repEmul_embed_leftinv τ') at 2.
    apply compat_lambda.
  Qed.

  Lemma compat_unit {Γ d n} :
    ⟪ Γ ⊩ S.unit ⟦ d , n ⟧ U.unit : ptunit ⟫.
  Proof.
    crush.
    unfold OfType, OfTypeStlc, OfTypeUtlc; split; crushTyping; intuition.
  Qed.

  Lemma compat_true {Γ d n} :
    ⟪ Γ ⊩ S.true ⟦ d , n ⟧ U.true : ptbool ⟫.
  Proof.
    crush.
    unfold OfType, OfTypeStlc, OfTypeUtlc; split; crushTyping; intuition.
  Qed.

  Lemma compat_false {Γ d n} :
    ⟪ Γ ⊩ S.false ⟦ d , n ⟧ U.false : ptbool ⟫.
  Proof.
    crush.
    unfold OfType, OfTypeStlc, OfTypeUtlc; split; crushTyping; intuition.
  Qed.

  Lemma OfType_pair {τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    OfType τ₁ ts₁ tu₁ →
    OfType τ₂ ts₂ tu₂ →
    OfType (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
    intros ot₁ ot₂.
    unfold OfType, OfTypeStlc in *.
    unfold OfTypeUtlc; crush.
  Qed.
  
  Lemma valrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    valrel d w τ₁ ts₁ tu₁ →
    valrel d w τ₂ ts₂ tu₂ →
    valrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
    intros vr₁ vr₂.
    crush;
      try match goal with 
          [ |- OfType (ptprod _ _) (S.pair _ _) (U.pair _ _)] => apply OfType_pair
      end; crush.
  Qed.

  Lemma termrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    termrel d w τ₁ ts₁ tu₁ →
    (forall w', w' ≤ w → termrel d w' τ₂ ts₂ tu₂) →
    termrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.
    change (S.pair _ _) with (S.pctx_app ts₁ (S.ppair₁ S.phole ts₂)).
    change (U.pair _ _) with (U.pctx_app tu₁ (U.ppair₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    destruct (valrel_implies_Value H) as [vvs₂ vvu₂].
    change (S.pair _ _) with (S.pctx_app ts₂ (S.ppair₂ vs S.phole)).
    change (U.pair _ _) with (U.pctx_app tu₂ (U.ppair₂ vu U.phole)).
    refine (termrel_ectx _ _ (tr₂ w' fw')  _); crush.
    eauto using valrel_in_termrel, valrel_mono, valrel_pair.
  Qed. 

  Lemma compat_pair {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : τ₁ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ S.pair ts₁ ts₂ ⟦ d , n ⟧ U.pair tu₁ tu₂ : ptprod τ₁ τ₂ ⟫.
  Proof.
    crush.
    apply termrel_pair; crush.
    refine (H1 w' _ _ _ _). 
    - unfold lev in *. omega.
    - eauto using envrel_mono.
  Qed.
 
  Lemma valrel_app {d w τ₁ τ₂ vs₁ vs₂ vu₁ vu₂} :
    valrel d w (ptarr τ₁ τ₂) vs₁ vu₁ →
    valrel d w τ₁ vs₂ vu₂ →
    termrel d w τ₂ (S.app vs₁ vs₂) (U.app vu₁ vu₂).
  Proof.
    intros vr₁ vr₂.
    rewrite -> valrel_fixp in vr₁.
    destruct vr₁ as [ot [tsb [tub [eq₁ [eq₂ bodyrel]]]]]; subst.
    destruct (valrel_implies_Value vr₂) as [vvs₂ vvu₂].
    assert (es : S.eval (S.app (S.abs (repEmul τ₁) tsb) vs₂) (tsb [beta1 vs₂])) by
        (refine (S.eval_ctx₀ S.phole _ I); refine (S.eval_beta vvs₂)).
    assert (es1 : S.evaln (S.app (S.abs (repEmul τ₁) tsb) vs₂) (tsb [beta1 vs₂]) 1) by 
        (eauto using S.evaln; omega).
    assert (eu : forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.app (U.abs tub) vu₂) Cu) (U.pctx_app (tub [beta1 vu₂]) Cu)) by
        (intros Cu eCu; refine (U.eval_ctx₀ Cu _ eCu); refine (U.eval_beta vvu₂)).
    assert (eu1 : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.app (U.abs tub) vu₂) Cu) (U.pctx_app (tub [beta1 vu₂]) Cu) 1) by 
        (eauto using U.evaln; omega).
    destruct w; try apply termrel_zero.
    refine (termrel_antired w es1 eu1 _ _ _); unfold lev in *; simpl; try omega.
    eapply bodyrel; try omega; eauto using valrel_mono.
  Qed.    
    

  Lemma termrel_app {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    termrel d w (ptarr τ₁ τ₂) ts₁ tu₁ →
    (forall w', w' ≤ w → termrel d w' τ₁ ts₂ tu₂) →
    termrel d w τ₂ (S.app ts₁ ts₂) (U.app tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.
    change (S.app _ _) with (S.pctx_app ts₁ (S.papp₁ S.phole ts₂)).
    change (U.app _ _) with (U.pctx_app tu₁ (U.papp₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    destruct (valrel_implies_Value H) as [vvs vvu].
    change (S.app _ _) with (S.pctx_app ts₂ (S.papp₂ vs S.phole)).
    change (U.app _ _) with (U.pctx_app tu₂ (U.papp₂ vu U.phole)).
    refine (termrel_ectx _ _ (tr₂ w' fw')  _); crush.
    replace _ with (valrel d w'0 τ₁ vs0 vu0) in H0 by eauto.
    refine (valrel_app _ H0).
    eauto using valrel_mono.
  Qed. 

  Lemma compat_app {Γ d n ts₁ tu₁ τ₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptarr τ₁ τ₂ ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₁ ⟫ →
    ⟪ Γ ⊩ S.app ts₁ ts₂ ⟦ d , n ⟧ U.app tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_app _ _); crush.
    refine (H1 w' _ _ _ _). 
    - unfold lev in *. omega.
    - eauto using envrel_mono.
  Qed.

  Lemma OfType_inl {τ₁ τ₂ ts tu} :
    OfType τ₁ ts tu →
    OfType (ptsum τ₁ τ₂) (S.inl ts) (U.inl tu).
  Proof.
    unfold OfType.
    destruct 1 as [ots otu].
    split; unfold OfTypeStlc in *; crush.
  Qed.
  
  Lemma termrel_inl {d w τ₁ τ₂ ts tu} :
    termrel d w τ₁ ts tu →
    termrel d w (ptsum τ₁ τ₂) (S.inl ts) (U.inl tu).
  Proof.
    intros tr.
    change (S.inl ts) with (S.pctx_app ts (S.pinl S.phole)).
    change (U.inl tu) with (U.pctx_app tu (U.pinl U.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    apply valrel_in_termrel;
    crush; 
    eauto using OfType_inl, valrel_implies_OfType.
  Qed.
    
  Lemma compat_inl {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₁ ⟫ →
    ⟪ Γ ⊩ S.inl ts ⟦ d , n ⟧ U.inl tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_inl _); crush.
  Qed.

  Lemma OfType_inr {τ₁ τ₂ ts tu} :
    OfType τ₂ ts tu →
    OfType (ptsum τ₁ τ₂) (S.inr ts) (U.inr tu).
  Proof.
    unfold OfType.
    destruct 1 as [ots otu].
    split; unfold OfTypeStlc in *; crush.
  Qed.
  
  Lemma termrel_inr {d w τ₁ τ₂ ts tu} :
    termrel d w τ₂ ts tu →
    termrel d w (ptsum τ₁ τ₂) (S.inr ts) (U.inr tu).
  Proof.
    intros tr.
    change (S.inr ts) with (S.pctx_app ts (S.pinr S.phole)).
    change (U.inr tu) with (U.pctx_app tu (U.pinr U.phole)).
    refine (termrel_ectx _ _ tr _); crush.
    apply valrel_in_termrel;
    crush; 
    eauto using OfType_inr, valrel_implies_OfType.
  Qed.
    
  Lemma compat_inr {Γ d n ts tu τ₁ τ₂} :
    ⟪ Γ ⊩ ts ⟦ d , n ⟧ tu : τ₂ ⟫ →
    ⟪ Γ ⊩ S.inr ts ⟦ d , n ⟧ U.inr tu : ptsum τ₁ τ₂ ⟫.
  Proof.
    crush.
    refine (termrel_inr _); crush.
  Qed.

  Lemma compat_var {Γ d n τ i} :
    ⟪ i : τ p∈ Γ ⟫ →
    ⟪ Γ ⊩ S.var i ⟦ d , n ⟧ U.var i : τ ⟫.
  Proof.
    intros iτ. constructor.
    - crushTyping.
      eauto using repEmulCtx_works.
    - intros ? _ ? ? er.
      apply valrel_in_termrel.
      refine (er _ _ iτ).
  Qed.
      
  Lemma termrel_seq {d w τ ts₁ ts₂ tu₁ tu₂} :
    termrel d w ptunit ts₁ tu₁ →
    (forall w', w' ≤ w → termrel d w' τ ts₂ tu₂) →
    termrel d w τ (S.seq ts₁ ts₂) (U.seq tu₁ tu₂).
  Proof.
    intros tr₁ tr₂.
    change (S.seq _ _) with (S.pctx_app ts₁ (S.pseq₁ S.phole ts₂)).
    change (U.seq _ _) with (U.pctx_app tu₁ (U.pseq₁ U.phole tu₂)).
    refine (termrel_ectx _ _ tr₁ _); crush.
    rewrite -> valrel_fixp in H.
    destruct H as [ot [eq₁ eq₂]]; subst.
    assert (S.eval (S.seq S.unit ts₂) ts₂) by 
        (apply (S.eval_ctx₀ S.phole); try refine (S.eval_seq_next _); simpl; intuition).
    assert (esn : S.evaln (S.seq S.unit ts₂) ts₂ 1) by eauto using S.evaln.
    assert (forall Cu, U.ECtx Cu → U.eval (U.pctx_app (U.seq U.unit tu₂) Cu) (U.pctx_app tu₂ Cu)) by 
        (intros Cu eCu; apply (U.eval_ctx₀ Cu); try refine (U.eval_seq_next _); simpl; intuition).
    assert (eun : forall Cu, U.ECtx Cu → U.evaln (U.pctx_app (U.seq U.unit tu₂) Cu) (U.pctx_app tu₂ Cu) 1) by eauto using U.evaln.
    refine (termrel_antired w' esn eun _ _ _); try omega.
    apply tr₂; intuition.
  Qed. 

  Lemma compat_seq {Γ d n ts₁ tu₁ ts₂ tu₂ τ₂} :
    ⟪ Γ ⊩ ts₁ ⟦ d , n ⟧ tu₁ : ptunit ⟫ →
    ⟪ Γ ⊩ ts₂ ⟦ d , n ⟧ tu₂ : τ₂ ⟫ →
    ⟪ Γ ⊩ S.seq ts₁ ts₂ ⟦ d , n ⟧ U.seq tu₁ tu₂ : τ₂ ⟫.
  Proof.
    crush.
    apply termrel_seq; crush.
    refine (H1 w' _ _ _ _). 
    - unfold lev in *. omega.
    - eauto using envrel_mono.
  Qed.
    
  Lemma erase_correct {Γ d n ts τ} :
    ⟪ Γ ⊢ ts : τ ⟫ →
    ⟪ embedCtx Γ ⊩ ts ⟦ d , n ⟧ erase ts : embed τ ⟫.
  Proof.
    induction 1; simpl; eauto using compat_inl, compat_inr, compat_pair, compat_lambda_embed, compat_app, compat_false, compat_true, compat_var, compat_unit, embedCtx_works, compat_seq.
    

End CompatibilityLemmas.