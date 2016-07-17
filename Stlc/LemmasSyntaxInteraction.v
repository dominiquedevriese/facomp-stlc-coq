Require Import Stlc.SpecSyntax.
Require Import Stlc.LemmasSyntaxBasic.
Require Import Stlc.LemmasWellScoping.

Require Import Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(** *** Renamings *)

Lemma wkl_wkr_comm (γ δ : Dom) :
  wkr γ >-> wkl δ = wkl δ >-> wkr γ.
Proof.
  extensionality i; unfold ren_comp.
  induction δ; crush.
Qed.

Lemma ren_ups_dunion ξ δ₁ δ₂ :
  (ξ ↑⋆ δ₁) ↑⋆ δ₂ = ξ ↑⋆ (δ₁ ∪ δ₂).
Proof.
  induction δ₂; crush.
  rewrite IHδ₂; crush.
Qed.
(* TODO: rewrite direction? *)

Lemma ren_ups_up ξ δ : (ξ ↑⋆ δ) ↑ = ξ ↑⋆ (S δ).
Proof. reflexivity. Qed.

Lemma wkl_comm δ ξ :
  ξ     >-> wkl δ =
  wkl δ >-> (ξ ↑⋆ δ).
Proof. extensionality i; crush. Qed.

Lemma apply_ren_beta_wkl (δ: Dom) :
  ∀ ξ i, (ren_beta δ ξ) (wkl δ i) = i.
Proof. induction δ; crush. Qed.
Hint Rewrite apply_ren_beta_wkl : infrastructure.

Lemma apply_ren_beta_wkr (γ δ: Dom) :
  ∀ ξ i, δ ∋ i → (ren_beta δ ξ) (wkr γ i) = ξ i.
Proof.
  induction δ; crush.
  apply (IHδ (S >-> ξ)); auto.
Qed.
Hint Rewrite apply_ren_beta_wkr : infrastructure.

Lemma wkl_ren_beta_cancel δ ξ :
  wkl δ >-> ren_beta δ ξ = ren_id.
Proof. extensionality i; crush. Qed.

Lemma ren_beta_comm δ ξ₁ ξ₂ :
  ren_beta δ ξ₁ >-> ξ₂                      =
  (ξ₂ ↑⋆ δ)     >-> ren_beta δ (ξ₁ >-> ξ₂).
Proof.
  extensionality i; cbn. revert ξ₁ ξ₂ i.
  induction δ; crush.
  destruct i; crush.
Qed.


(** *** Substitution *)

Lemma sub_eta (ζ: Sub) : (⌈wkl 1⌉ >=> ζ) · ζ 0 = ζ.
Proof. extensionality i; destruct i; reflexivity. Qed.
(* Hint Rewrite sub_eta : infrastructure. *)

Lemma sub_reflection ζ t : ⌈wkl 1⌉ >=> (ζ · t) = ζ.
Proof. extensionality i; destruct i; reflexivity. Qed.
(* Hint Rewrite sub_reflection : infrastructure. *)

Lemma sub_wkl1_snoc0 : ⌈wkl 1⌉ · var 0 = sub_id.
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma sub_comp_snoc ζ₁ ζ₂ t :
  (ζ₁ · t) >=> ζ₂ = (ζ₁ >=> ζ₂) · t[ζ₂].
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma apply_sub_beta_wkl (δ: Dom) :
  ∀ ζ i, (sub_beta δ ζ) (wkl δ i) = var i.
Proof. induction δ; crush. Qed.
Hint Rewrite apply_sub_beta_wkl : infrastructure.

Lemma apply_sub_beta_wkr (γ δ: Dom) :
  ∀ ζ i, δ ∋ i → (sub_beta δ ζ) (wkr γ i) = ζ i.
Proof.
  induction δ; crush.
  destruct i; crush.
  apply (IHδ (⌈wkl 1⌉ >=> ζ)); auto.
Qed.
Hint Rewrite apply_sub_beta_wkr : infrastructure.

Lemma wkl_sub_beta_cancel δ ζ :
  ⌈wkl δ⌉ >=> (sub_beta δ ζ) = sub_id.
Proof. extensionality i; crush. Qed.

Lemma sub_beta_comm δ ζ₁ ζ₂ :
  sub_beta δ ζ₁ >=> ζ₂                     =
  (ζ₂ ↑⋆ δ)     >=> sub_beta δ (ζ₁ >=> ζ₂).
Proof.
  extensionality i. revert ζ₁ ζ₂ i.
  induction δ.
  - crush.
  - intros ζ₁ ζ₂ i. destruct i; crush.
    + rewrite IHδ.
      reflexivity.
Qed.

Lemma sub_beta1_comm t ζ :
  sub_beta1 t >=> ζ                =
  (ζ ↑)       >=> sub_beta1 t[ζ].
Proof. apply (sub_beta_comm 1). Qed.

Lemma subst0_comm t₁ t₂ ζ :
  (subst0 t₁ t₂)[ζ] =
  subst0 t₁[ζ] t₂[ζ↑].
Proof.
  unfold subst0; crush.
  f_equal; auto using sub_beta1_comm.
Qed.
Hint Rewrite subst0_comm : infrastructure.

(* Local Variables: *)
(* coq-load-path: (("." "Stlc")) *)
(* End: *)
