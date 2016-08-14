Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Utlc.SpecScoping.
Require Import Utlc.LemmasScoping.
Require Import LogRel.PseudoType.
Require Import LogRel.LR.
Require Import LogRel.LemmasLR.
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

(* Domi: it would be more convenient to define envrel similar to WtSub using
   something like GetEVar. Perhaps generalize GetEVar *)
(* Lemma envrel_implies_WtSub {d W Γ γs γu} : *)
(*   envrel d W Γ γs γu → WtSub (repEmulCtx Γ) empty γs. *)
(* Proof. *)
(*   Print WtSub. *)
(*   intros envrel i τ vi_τ. *)
(*   Print envrel. *)


(* Section CompatibilityLemmas. *)
(*   Lemma compat_lambda {Γ τ' ts d n tu τ} : *)
(*     ⟪ Γ p▻ τ' ⊩ ts ⟦ d , n ⟧ tu : τ ⟫ → *)
(*     ⟪ Γ ⊩ (S.abs (repEmul τ') ts) ⟦ d , n ⟧ abs tu : ptarr τ' τ ⟫. *)
(*   Proof. *)
(*     intros lr. *)
(*     unfold OpenLRN in *. *)
(*     destruct_conjs. *)
(*     split; crushTyping. *)
(*     apply valrel_in_termrel. *)
(*     unfold valrel, valrel'. *)
(*     unfold well_founded_induction_type, Acc_rect. *)
(*     unfold valrel'' in |- *. *)
(*     simpl. *)
(*     split. *)
(*     -  unfold OfType, OfTypeStlc, OfTypeUtlc; split. *)
(*        + replace (S.abs (repEmul τ') (ts [γs↑])) with ((S.abs (repEmul τ') ts) [γs]). *)
(*          refine (S.typing_sub _ _ _ _); crushTyping. *)
         

(* End CompabilityLemmas. *)