Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import LogRel.PseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
Require Import Omega.
Require Utlc.Fix.

Module S.
    Include Stlc.SpecSyntax.
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

Lemma extend_envrel {d w Γ γs γu τ ts tu} :
  valrel d w τ ts tu →
  envrel d w Γ γs γu →
  envrel d w (Γ p▻ τ) (γs↑ >=> beta1 ts) (γu↑ >=> beta1 tu).
Admitted.

Local Ltac crush :=
  repeat (repeat match goal with
                  [ |- _ ∧ _ ] => split
                | [ |- ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ ] => (unfold OpenLRN; split)
                | [ H : ⟪ _ ⊩ _ ⟦ _ , _ ⟧ _ : _ ⟫ |- _ ] => (unfold OpenLRN in H; destruct_conjs)
                | [ |- termrel _ _ _ (S.abs _ _) (U.abs _) ] => apply valrel_in_termrel
                | [ |- termrel _ _ _ S.unit U.unit ] => apply valrel_in_termrel
                | [ |- termrel _ _ _ S.false U.false ] => apply valrel_in_termrel
                | [ |- termrel _ _ _ S.true U.true ] => apply valrel_in_termrel
                | [ |- valrel _ _ _ _ _] => rewrite -> valrel_fixp; unfold valrel'; cbn
                | [ |- exists tsb tub, S.abs _ ?tsb' = S.abs _ tsb ∧ U.abs ?tub' = U.abs tub ∧ _] => exists tsb'; exists tub'; split; intuition
                | [ |- exists t', U.abs ?t = U.abs t' ] => exists t; intuition
                | [ |- S.ECtx (S.pctx_cat _ _) ] => apply S.ectx_cat
                | [ |- U.ECtx (U.pctx_cat _ _) ] => apply U.ectx_cat
              end;
          crushTyping;
          intuition).

Lemma OfTypeUtlc_implies_Value {τ tu} :
  OfTypeUtlc τ tu →
  U.Value tu.
Proof.
  revert tu; induction τ;
  intros tu ot; unfold OfTypeUtlc in ot; subst; crush; subst; crush.
  - (* ptarr *)
    destruct ot as [t' eq]; subst.
    crush.
  - destruct ot as [tu₁ [tu₂ [equ [ot₁ ot₂]]]].
    subst; crush.
  - destruct H as [tu' [eq' ot']].
    subst; crush.
  - destruct H as [tu' [eq' ot']].
    subst; crush.
Qed. 

Lemma OfType_implies_Value {τ ts tu} :
  OfType τ ts tu →
  S.Value ts ∧ U.Value tu.
Proof.
  unfold OfType, OfTypeStlc, OfTypeUtlc.
  intros ot; destruct_conjs;
  eauto using OfTypeUtlc_implies_Value.
Qed.

Lemma valrel_implies_Value {d w τ ts tu} :
  valrel d w τ ts tu →
  S.Value ts ∧ U.Value tu.
Proof.
  intros vr.
  rewrite -> valrel_fixp in vr.
  destruct vr as [ot _].
  exact (OfType_implies_Value ot).
Qed.

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

  Lemma valrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    valrel d w τ₁ ts₁ tu₁ →
    valrel d w τ₂ ts₂ tu₂ →
    valrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
  Admitted.

  Lemma termrel_pair {d w τ₁ τ₂ ts₁ ts₂ tu₁ tu₂} :
    termrel d w τ₁ ts₁ tu₁ →
    (forall w', w' ≤ w → termrel d w' τ₂ ts₂ tu₂) →
    termrel d w (ptprod τ₁ τ₂) (S.pair ts₁ ts₂) (U.pair tu₁ tu₂).
  Proof.
    intros tr₁ tr₂ Cs Cu eCs eCu cr.
    replace (S.pctx_app (S.pair ts₁ ts₂) Cs) with (S.pctx_app ts₁ (S.pctx_cat (S.ppair₁ S.phole ts₂) Cs)) by apply S.pctx_cat_app.
    replace (U.pctx_app (U.pair tu₁ tu₂) Cu) with (U.pctx_app tu₁ (U.pctx_cat (U.ppair₁ U.phole tu₂) Cu)) by apply U.pctx_cat_app.
    refine (tr₁ (S.pctx_cat (S.ppair₁ S.phole ts₂) Cs) (U.pctx_cat (U.ppair₁ U.phole tu₂) Cu) _ _ _); crush.
    intros w' fw' vs₁ vu₁ vr₁.
    destruct (valrel_implies_Value vr₁) as [vvs₁ vvu₁].
    replace (S.pctx_app vs₁ (S.pctx_cat (S.ppair₁ S.phole ts₂) Cs)) with (S.pctx_app ts₂ (S.pctx_cat (S.ppair₂ vs₁ S.phole) Cs)) by (rewrite -> ?S.pctx_cat_app; auto).
    replace (U.pctx_app vu₁ (U.pctx_cat (U.ppair₁ U.phole tu₂) Cu)) with (U.pctx_app tu₂ (U.pctx_cat (U.ppair₂ vu₁ U.phole) Cu)) by (rewrite -> ?U.pctx_cat_app; auto).
    refine (tr₂ w' _ (S.pctx_cat (S.ppair₂ vs₁ S.phole) Cs) (U.pctx_cat (U.ppair₂ vu₁ U.phole) Cu) _ _ _); crush.
    intros w'' fw'' vs₂ vu₂ vr₂.
    destruct (valrel_implies_Value vr₂) as [vvs₂ vvu₂].
    replace (S.pctx_app vs₂ (S.pctx_cat (S.ppair₂ vs₁ S.phole) Cs)) with (S.pctx_app (S.pair vs₁ vs₂) Cs) by (symmetry; apply S.pctx_cat_app).
    replace (U.pctx_app vu₂ (U.pctx_cat (U.ppair₂ vu₁ U.phole) Cu)) with (U.pctx_app (U.pair vu₁ vu₂) Cu) by (symmetry; apply U.pctx_cat_app).
    refine (cr w'' _ (S.pair vs₁ vs₂) (U.pair vu₁ vu₂) _).
    - omega.
    - apply valrel_pair; eauto using valrel_mono.
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
 

End CompatibilityLemmas.