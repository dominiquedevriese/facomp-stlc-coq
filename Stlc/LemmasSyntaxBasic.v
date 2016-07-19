Require Import Stlc.SpecSyntax.

Require Import Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

Create HintDb infrastructure.
Create HintDb ws.

Ltac crushRewriteH :=
  autorewrite with infrastructure in *.

Ltac crushSyntaxMatchH :=
  match goal with
    | [ H: S _ = S _             |- _ ] => apply eq_add_S in H
    | [ H: tarr _ _  = tarr _ _  |- _ ] => inversion H; clear H
    | [ H: tprod _ _ = tprod _ _ |- _ ] => inversion H; clear H
    | [ H: tsum _ _ = tsum _ _   |- _ ] => inversion H; clear H
    | [ |- S _          = S _          ] => f_equal
    | [ |- var _        = var _        ] => f_equal
    | [ |- abs _ _      = abs _ _      ] => f_equal
    | [ |- app _ _      = app _ _      ] => f_equal
    | [ |- unit         = unit         ] => reflexivity
    | [ |- true         = true         ] => reflexivity
    | [ |- false        = false        ] => reflexivity
    | [ |- ite _ _ _    = ite _ _ _    ] => f_equal
    | [ |- pair _ _     = pair _ _     ] => f_equal
    | [ |- proj₁ _      = proj₁ _      ] => f_equal
    | [ |- proj₂ _      = proj₂ _      ] => f_equal
    | [ |- inl _        = inl _        ] => f_equal
    | [ |- inr _        = inr _        ] => f_equal
    | [ |- caseof _ _ _ = caseof _ _ _ ] => f_equal
    | [ |- seq _ _      = seq _ _      ] => f_equal
    | [ |- fixt _ _ _   = fixt _ _ _   ] => f_equal
    | [ |- _ ▻ _        = _ ▻ _        ] => f_equal
    (* | |- context[applyRenTm ?ξ ?t] => *)
    (*     change (applyRenTm ξ t) with (t[ξ]) *)
    (* | |- context[applySubTm ?ζ ?t] => *)
    (*     change (applySubTm ζ t) with (t[ζ]) *)
  end.

Ltac crush :=
  intros;
  repeat
    (cbn in *;
     repeat crushRewriteH;
     repeat crushSyntaxMatchH);
  auto.

(** *** Domains *)

Lemma dunion_assoc (δ₁ δ₂ δ₃: Dom) :
  δ₁ ∪ (δ₂ ∪ δ₃) = (δ₁ ∪ δ₂) ∪ δ₃.
Proof. induction δ₃; crush. Qed.
Hint Rewrite dunion_assoc : infrastructure.


(** *** Indices *)

Lemma wkl_zero :
  wkl 0 = ren_id.
Proof. reflexivity. Qed.
Hint Rewrite wkl_zero : infrastructure.

Lemma wkl_dunion (δ₁ δ₂: Dom) :
  wkl (δ₁ ∪ δ₂) = wkl δ₁ >-> wkl δ₂.
Proof.
  extensionality i; unfold ren_comp.
  induction δ₂; crush.
Qed.
Hint Rewrite wkl_dunion : infrastructure.

Lemma wkr_zero :
  wkr 0 = ren_id.
Proof.
  extensionality i; unfold ren_id.
  induction i; crush.
Qed.
Hint Rewrite wkr_zero : infrastructure.

Lemma wkr_dunion (δ₁ δ₂: Dom) :
  wkr (δ₁ ∪ δ₂) = wkr δ₂ >-> wkr δ₁.
Proof.
  extensionality i; unfold ren_comp.
  induction i; crush.
Qed.
Hint Rewrite wkr_dunion : infrastructure.


(** *** Renaming *)

Lemma apply_ren_ups_wkl (ξ: Ren) (δ: Dom) (i: Ix) :
  (ξ ↑⋆ δ) (wkl δ i) = wkl δ (ξ i).
Proof. induction δ; crush. Qed.
Hint Rewrite apply_ren_ups_wkl : infrastructure.

Lemma ren_id_up : ren_id ↑ = ren_id.
Proof. extensionality i; destruct i; auto. Qed.
Hint Rewrite ren_id_up : infrastructure.

Lemma ren_id_ups (δ: Dom) : ren_id ↑⋆ δ = ren_id.
Proof.
  induction δ; crush.
  rewrite IHδ; crush.
Qed.
Hint Rewrite ren_id_ups : infrastructure.

Lemma renTm_id t : t[ren_id] = t.
Proof. induction t; crush. Qed.
Hint Rewrite renTm_id : infrastructure.

Lemma ren_comp_id_right ξ :
  ξ >-> ren_id = ξ.
Proof. auto. Qed.
Hint Rewrite ren_comp_id_right : infrastructure.

Lemma ren_comp_id_left ξ :
  ren_id >-> ξ = ξ.
Proof. auto. Qed.
Hint Rewrite ren_comp_id_left : infrastructure.

Lemma ren_comp_up ξ₁ ξ₂ :
  (ξ₁ >-> ξ₂) ↑ = (ξ₁ ↑) >-> (ξ₂ ↑).
Proof. extensionality i; destruct i; crush. Qed.
Hint Rewrite ren_comp_up : infrastructure.

Lemma ren_comp_ups δ ξ₁ ξ₂ :
  (ξ₁ >-> ξ₂) ↑⋆ δ = (ξ₁ ↑⋆ δ) >-> (ξ₂ ↑⋆ δ).
Proof.
  induction δ; crush.
  rewrite IHδ; crush.
Qed.
Hint Rewrite ren_comp_ups : infrastructure.

Lemma renTm_comp t :
  ∀ ξ₁ ξ₂, t[ξ₁][ξ₂] = t[ξ₁ >-> ξ₂].
Proof. induction t; crush. Qed.
Hint Rewrite renTm_comp : infrastructure.

(* Always try to associate to the left in rewriting. *)
Lemma ren_comp_assoc ξ₁ ξ₂ ξ₃ :
  ξ₁ >-> (ξ₂ >-> ξ₃) = (ξ₁ >-> ξ₂) >-> ξ₃.
Proof. auto. Qed.
Hint Rewrite ren_comp_assoc : infrastructure.


(** *** Substitution *)

Lemma apply_sub_ups_wkl (ζ: Sub) (δ: Dom) (i: Ix) :
  (ζ ↑⋆ δ) (wkl δ i) = (ζ i)[wkl δ].
Proof.
  induction δ; crush.
  rewrite IHδ; crush.
Qed.
Hint Rewrite apply_sub_ups_wkl : infrastructure.

Lemma ren_toSub_up ξ : ⌈ξ⌉ ↑ = ⌈ξ ↑⌉.
Proof. extensionality i; destruct i; crush. Qed.
Hint Rewrite ren_toSub_up : infrastructure.

Lemma renTm_toSub t : ∀ ξ, t[⌈ξ⌉] = t[ξ].
Proof. induction t; crush. Qed.
Hint Rewrite renTm_toSub : infrastructure.

Lemma sub_toSub_ren_id  : ⌈ren_id⌉ = sub_id.
Proof. reflexivity. Qed.
Hint Rewrite sub_toSub_ren_id : infrastructure.

Lemma sub_comp_ren_id ζ :
  sub_comp_ren ζ ren_id = ζ.
Proof. extensionality i; unfold sub_comp_ren; crush. Qed.
Hint Rewrite sub_comp_ren_id : infrastructure.

(* We can now use, this lemma as the "definition" of sub_comp_ren. *)
Lemma sub_comp_ren_def (ζ: Sub) (ξ: Ren) :
  sub_comp_ren ζ ξ = ζ >=> ⌈ξ⌉.
Proof. extensionality i; eauto using renTm_toSub. Qed.
Hint Rewrite sub_comp_ren_def : infrastructure.

Lemma sub_id_up : sub_id ↑ = sub_id.
Proof. extensionality i; destruct i; auto. Qed.
Hint Rewrite sub_id_up : infrastructure.

Lemma sub_id_ups (δ: Dom) : sub_id ↑⋆ δ = sub_id.
Proof.
  induction δ; crush.
  rewrite IHδ; crush.
Qed.
Hint Rewrite sub_id_ups : infrastructure.

Lemma subTm_id t : t[sub_id] = t.
Proof. induction t; crush. Qed.
Hint Rewrite subTm_id : infrastructure.

Lemma sub_comp_id_right ζ :
  ζ >=> sub_id = ζ.
Proof. extensionality i. crush. Qed.
Hint Rewrite sub_comp_id_right : infrastructure.

Lemma sub_comp_id_left ζ :
  sub_id >=> ζ = ζ.
Proof. auto. Qed.
Hint Rewrite sub_comp_id_left : infrastructure.

(* Lemma sub_up_def ζ : *)
(*   ζ ↑ = (ζ >=> ⌈wkl 1⌉) · var 0. *)
(* Proof. unfold up, sub_up; crush. Qed. *)

Lemma ren_comp_sub_up ζ ξ :
  (⌈ξ⌉ >=> ζ) ↑ = ⌈ξ↑⌉ >=> ζ↑.
Proof. extensionality i; destruct i; reflexivity. Qed.
Hint Rewrite ren_comp_sub_up : infrastructure.

Lemma subTm_comp_ren_sub t :
  ∀ ξ ζ, t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
Proof. induction t; crush. Qed.
Hint Rewrite subTm_comp_ren_sub : infrastructure.

Lemma comp_ren_ren_toSub ξ₁ ξ₂ :
  ⌈ξ₁⌉ >=> ⌈ξ₂⌉ = ⌈ξ₁ >-> ξ₂⌉.
Proof. extensionality i; reflexivity. Qed.
Hint Rewrite comp_ren_ren_toSub : infrastructure.

Lemma sub_comp_ren_up ζ ξ :
  (ζ >=> ⌈ξ⌉) ↑ = (ζ ↑) >=> ⌈ξ↑⌉.
Proof. extensionality i; destruct i; crush. Qed.
Hint Rewrite sub_comp_ren_up : infrastructure.

Lemma subTm_sub_comp_ren t :
  ∀ ξ ζ, t[ζ][ξ] = t[ζ >=> ⌈ξ⌉].
Proof. induction t; crush. Qed.
Hint Rewrite subTm_sub_comp_ren : infrastructure.

Lemma sub_comp_up ζ₁ ζ₂ :
  (ζ₁ >=> ζ₂) ↑ = (ζ₁ ↑) >=> (ζ₂ ↑).
Proof.
  extensionality i; destruct i; crush.
  - f_equal. extensionality j; crush.
Qed.
Hint Rewrite sub_comp_up : infrastructure.

Lemma sub_comp_ups δ ζ₁ ζ₂ :
  (ζ₁ >=> ζ₂) ↑⋆ δ = (ζ₁ ↑⋆ δ) >=> (ζ₂ ↑⋆ δ).
Proof.
  induction δ; crush.
  rewrite IHδ; crush.
Qed.
Hint Rewrite sub_comp_ups : infrastructure.

Lemma subTm_comp t :
  ∀ ζ₁ ζ₂, t[ζ₁][ζ₂] = t[ζ₁ >=> ζ₂].
Proof. induction t; crush. Qed.
Hint Rewrite subTm_comp : infrastructure.

(* Always try to associate to the left in rewriting. *)
Lemma sub_comp_assoc ζ₁ ζ₂ ζ₃ :
  ζ₁ >=> (ζ₂ >=> ζ₃) = (ζ₁ >=> ζ₂) >=> ζ₃.
Proof. extensionality i; crush. Qed.
Hint Rewrite sub_comp_assoc : infrastructure.

(** *** Environments *)

Lemma ecat_assoc (Γ₁ Γ₂ Γ₃: Env) :
  Γ₁ ▻▻ (Γ₂ ▻▻ Γ₃) = (Γ₁ ▻▻ Γ₂) ▻▻ Γ₃.
Proof. induction Γ₃; crush. Qed.
Hint Rewrite ecat_assoc : infrastructure.

Lemma dom_ecat (Γ₁ Γ₂: Env) :
  dom (Γ₁ ▻▻ Γ₂) = dom Γ₁ ∪ dom Γ₂.
Proof. induction Γ₂; crush. Qed.
Hint Rewrite dom_ecat : infrastructure.

(* Local Variables: *)
(* coq-load-path: (("." "Stlc")) *)
(* End: *)
