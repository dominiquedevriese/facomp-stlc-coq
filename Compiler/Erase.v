Require Stlc.SpecSyntax.
Require Utlc.SpecSyntax.
Require Import Stlc.SpecTyping.
Require Import Stlc.LemmasTyping.
Require Import Utlc.SpecScoping.
Require Utlc.Fix.

Module SS := Stlc.SpecSyntax.
Module US := Utlc.SpecSyntax.
Module UF := Utlc.Fix.

Fixpoint erase (t : SS.Tm) : US.UTm :=
  match t with
    | SS.abs τ t         => US.abs (erase t)
    | SS.unit            => US.unit
    | SS.true            => US.true
    | SS.false           => US.false
    | SS.pair t₁ t₂      => US.pair (erase t₁) (erase t₂)
    | SS.inl t           => US.inl (erase t)
    | SS.inr t           => US.inr (erase t)
    | SS.var x           => US.var x
    | SS.app t₁ t₂       => US.app (erase t₁) (erase t₂)
    | SS.ite t₁ t₂ t₃    => US.ite (erase t₁) (erase t₂) (erase t₃)
    | SS.proj₁ t₁        => US.proj₁ (erase t₁)
    | SS.proj₂ t₁        => US.proj₂ (erase t₁)
    | SS.caseof t₁ t₂ t₃ => US.caseof (erase t₁) (erase t₂) (erase t₃)
    | SS.seq t₁ t₂       => US.seq (erase t₁) (erase t₂)
    | SS.fixt _ _ t₁     => US.app UF.ufix (erase t₁)
  end.


Lemma erase_scope (t : SS.Tm) (Γ : SS.Env) (τ : SS.Ty) :
  ⟪ Γ ⊢ t : τ ⟫ -> ⟨ dom Γ ⊢ erase t ⟩.
Proof.
  revert Γ τ.
  induction t; intros Γ τ' H; inversion H; clear H; simpl; constructor.
  * exact (getEvar_wsIx _ _ _ H1).
  * exact (IHt _ _ H3).
  * exact (IHt1 _ _ H2).
  * exact (IHt2 _ _ H4).
  * exact (IHt1 _ _ H3).
  * exact (IHt2 _ _ H5).
  * exact (IHt3 _ _ H6).
  * exact (IHt1 _ _ H2).
  * exact (IHt2 _ _ H4).
  * exact (IHt _ _ H1).
  * exact (IHt _ _ H1).
  * exact (IHt _ _ H1).
  * exact (IHt _ _ H1).
  * exact (IHt1 _ _ H3).
  * exact (IHt2 _ _ H5).
  * exact (IHt3 _ _ H6).
  * exact (IHt1 _ _ H2).
  * exact (IHt2 _ _ H4).
  * apply UF.ufix_ws.
  * exact (IHt _ _ H4).
Qed.