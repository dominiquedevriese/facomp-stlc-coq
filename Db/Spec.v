Require Export Coq.Unicode.Utf8.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

Set Maximal Implicit Insertion.

(* Function composition. *)
Definition fcomp {X Y Z: Type} (f: X → Y) (g: Y → Z) : X → Z :=
  fun x => g (f x).
Arguments fcomp {_ _ _} f g i /.
Notation "f >-> g" := (fcomp f g) (at level 56).

(* Injectivity property. *)
Definition Inj {A B} (f: A → B) : Prop :=
  ∀ x y, f x = f y → x = y.

(** * Basic definitions

    This Section contains basic definitions for the de Bruijn representation
    of the abstract syntax.  *)

(** ** Domains *)

(** [Dom] is the representation of domains of typing contexts
    or of simultaneous renamings/substitutions. For the de
    Bruijn representation with a single sort with variables,
    we can represent domains as natural numbers. *)
Definition Dom: Set := nat.

Fixpoint dunion (δ₁ δ₂: Dom) {struct δ₂} : Dom :=
  match δ₂ with
    | O    => δ₁
    | S δ₂ => S (dunion δ₁ δ₂)
  end.
Notation "δ₁ ∪ δ₂" := (dunion δ₁ δ₂) (at level 55, left associativity).

Section FoldlDom.

  Context {X : Type}.
  Variable s : X → X.

  Fixpoint foldlDom (δ: Dom) (x: X) : X :=
    match δ with
      | O   => x
      | S δ => foldlDom δ (s x)
    end.

End FoldlDom.

(** ** De Bruijn indices. *)
Definition Ix : Set := nat.

Reserved Notation "γ ∋ i" (at level 80).
Inductive wsIx : Dom → Ix → Prop :=
  | ws0 γ   :         S γ ∋ 0
  | wsS γ i : γ ∋ i → S γ ∋ S i
where "γ ∋ i" := (wsIx γ i).

(** ** Substitutions

    Substitutions are mapping from indices to values. The argument of 'Sub'
    indicates the sort of the substitures. A renaming is simply a substitution
    that substitutes indices for indices 'Sub Ix'.
 *)

Definition Sub (X: Type) : Type := Ix → X.
Definition snoc {X: Type} (ξ: Sub X) (x: X) : Sub X :=
  fun i =>
    match i with
      | O   => x
      | S i => ξ i
    end.
Notation "ξ · x" := (snoc ξ x) (at level 55, left associativity).
Arguments snoc {_} ξ x !i.

(** * Syntax related type-classes *)

Section Vars.

  (** Class for syntactic sorts with variables. *)
  Class Vr (X: Type) :=
    { vr: Sub X;
      vr_inj: Inj vr
    }.
  Arguments vr {_ _} i.

  Definition idm X {vrX: Vr X} : Sub X := vr.
  Global Arguments idm _ {_} i /.

End Vars.

Section Weaken.

  (** Class for syntactic sorts that can be weakened. *)
  Class Wk (X: Type) {vrX: Vr X} :=
    { wk: X → X;
      wk_inj: Inj wk;
      wk_vr: ∀ (i: Ix), wk (vr i) = vr (S i)
    }.
  Global Arguments wk {_ _ _} x.
  Definition wk_vr' := @wk_vr.

  Context {X: Type}.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.

  Fixpoint wks (δ: Dom) (x: X) {struct δ} : X :=
    match δ with
      | O   => x
      | S δ => wk (wks δ x)
    end.
  Global Arguments wks !δ x /.

  Definition wkm : Sub X := vr >-> wk.
  Global Arguments wkm i/.

  Fixpoint wkms (δ: Dom) {struct δ} : Sub X :=
    match δ with
      | O   => idm X
      | S δ => wkms δ >-> wk
    end.

  Definition up (ξ: Sub X) : Sub X :=
    (ξ >-> wk) · vr 0.
  Global Arguments up ξ !i /.

  Fixpoint ups (ξ: Sub X) (δ: Dom) {struct δ} : Sub X :=
    match δ with
      | O   => ξ
      | S δ => up (ups ξ δ)
    end.
  Global Arguments ups ξ !δ / i.

End Weaken.

Notation "ξ ↑" := (up ξ)
  (at level 8, left associativity, format "ξ ↑").
Notation "x ↑⋆ δ" := (ups x δ)
  (at level 53, left associativity).

Section Lift.

  (* Lifting terms of sort X to terms of sort Y. *)
  Class Lift (X Y: Type) {vrX: Vr X} {vrY: Vr Y} :=
    { lift: X → Y;
      lift_inj: Inj lift;
      lift_vr: ∀ (i: Ix), lift (vr i) = vr i
    }.

  Context {X: Type}.
  Context {vrX: Vr X}.

  Global Instance liftXX : Lift X X := {| lift := fun x => x |}.
  Proof. unfold Inj; auto. reflexivity. Defined.

  Lemma liftXX_id (x: X) : lift x = x.
  Proof. reflexivity. Qed.
  Global Opaque liftXX.

  Context {Y: Type}.
  Context {vrY: Vr Y}.
  Context {liftXY: Lift X Y}.

  Definition liftSub (ξ: Sub X) : Sub Y :=
    ξ >-> lift.
  Global Arguments liftSub ξ i /.

End Lift.

Notation "⌈ ξ ⌉" := (liftSub ξ) (format "⌈ ξ ⌉").

Reserved Notation "t '[' ξ ']'"
  (at level 8, left associativity, format "t [ ξ ]").
Reserved Notation "ξ >=> ζ" (at level 56).

Section Application.

  (** Application of a substitution for sort Y to a term of sort X. *)
  Class Ap (X Y: Type) {vrY: Vr Y} :=
    { ap: Sub Y → X → X;
      ap_id: ∀ (x: X), ap (idm Y) x = x;
    }.
  Global Arguments ap {_ _ _ _} ζ !t /.
  Notation "t '[' ξ ']'" := (ap ξ t).

  Definition comp {X Y} {vrY: Vr Y} {apXY: Ap X Y}
    (ξ: Sub X) (ζ: Sub Y) : Sub X := fun i => (ξ i)[ζ].
  Global Arguments comp {_ _ _ _} ξ ζ i /.
  Notation "ξ >=> ζ" := (comp ξ ζ).

End Application.

Notation "t '[' ξ ']'" := (ap ξ t).
Notation "ξ >=> ζ" := (comp ξ ζ).

(* Class Subst (X: Type) {vrX: Vr X} {wkX: Wk X} {ap_X: Ap X X} := {}. *)

(** ** Ix Instances *)
Section Indices.

  Global Instance vrIx: Vr Ix := {| vr := fun i => i |}.
  Proof. unfold Inj; auto. Defined.
  Global Instance wkIx: Wk Ix := {| wk := S |}.
  Proof. unfold Inj; auto. reflexivity. Defined.
  Global Instance apIxIx: Ap Ix Ix := {| ap := fun ξ i => ξ i |}.
  Proof. reflexivity. Defined.
  Global Instance liftIx {X} {vrX: Vr X}: Lift Ix X := {| lift := vr |}.
  Proof. apply vr_inj. reflexivity. Defined.
  (* Global Instance sbIx: Subst Ix. *)

  (* The concrete weakening function 'wk' should be considered as an
     implementation detail and the user code should only ever see the abstract
     weakening morphism 'wkm'. Especially on indices the function constantly
     pops up during simplifications and often even reduces to an application of
     the successor constructor 'S'. To avoid this we capture the essentials of
     the 'wk' on indices in the following lemmas and make the 'Wk Ix' instance
     opaque to prevent simplification.

     The first two lemmas encode the reduction behaviour of snoc and up in the
     successor case. The remaining lemmas replace occurrences of 'wk' in
     contexts a substitution is expected by occurrences of the abstract
     weakening 'wkm'.

     In the case of an "unsnoc" operation -- such as in the definition of
     beta -- the successor constructor should be used instead of 'wk'.
   *)

  Lemma snoc_wk (X: Type) (ζ: Sub X) (x: X) (i : Ix) :
    snoc ζ x (wk i) = ζ i.
  Proof. reflexivity. Qed.

  Lemma up_wk (X: Type) {vrX: Vr X} {wkX: Wk X} (ζ: Sub X) (i : Ix) :
    (up ζ) (wk i) = wk (ζ i).
  Proof. reflexivity. Qed.

  Lemma wk_up : wk↑ = wkm↑.
  Proof. reflexivity. Qed.

  Lemma wk_ups (δ: Dom) : wk ↑⋆ δ = wkm ↑⋆ δ.
  Proof. reflexivity. Qed.

  Lemma wk_ap (X: Type) {apX: Ap X Ix} (x: X) : x[wk] = x[wkm].
  Proof. reflexivity. Qed.

  Lemma wk_liftSub (X: Type) {vrX: Vr X} : ⌈wk⌉ = ⌈wkm⌉.
  Proof. reflexivity. Qed.

  Global Opaque wkIx.

End Indices.

Hint Rewrite snoc_wk : infrastructure.
Hint Rewrite wk_up : infrastructure.
Hint Rewrite wk_ups : infrastructure.

(** ** Beta substitution *)
Section Beta.

  Context {X: Type}.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.

  (* Substitute the last δ variables by values determined by 'ζ' and
     leave the remaining variables alone. This means if (ζ: Δ => Γ)
     and (δ = dom Δ) then (beta δ ζ: Γ ,Δ => Γ).
  *)
  Fixpoint beta (δ: Dom) (ζ: Sub X) {struct δ} : Sub X :=
    match δ with
      | O   => idm X
      | S δ => snoc (beta δ (S >-> ζ)) (ζ 0)
    end.
  Global Arguments beta !δ ζ i/.

  Definition beta1 : X → Sub X :=
    fun x => beta 1 (idm X · x).
  Global Arguments beta1 x i/.

End Beta.

Class Ws (T: Type) := ws: Dom → T → Prop.
Notation "⟨  γ ⊢ t  ⟩" := (ws γ t) (at level 0, γ at level 99, t at level 99).

Instance WsIx : Ws Ix := { ws := wsIx }.

Definition WsSub {X} {wsX: Ws X} (γ δ: Dom) (ξ: Sub X) : Prop :=
  ∀ (i: Ix), γ ∋ i → ⟨ δ ⊢ ξ i ⟩.
Notation "⟨ ξ : γ => δ ⟩" := (WsSub γ δ ξ)
 (at level 0, ξ at level 99, γ at level 99, δ at level 99).

Section Unused.

  Class WsVr (X: Type) {wsX: Ws X} {vrX: Vr X} :=
    {wsVr: ∀ (δ: Dom) (i: Ix), δ ∋ i → ⟨ δ ⊢ (vr (X := X) i) ⟩}.
  Class WsWk (X: Type) {wsX: Ws X} {vrX: Vr X} {wkX: Wk X} :=
    {wsWk: ∀ (δ: Dom) (x: X), ⟨ δ ⊢ x ⟩ → ⟨ S δ ⊢ wk x ⟩}.
  Class WsiWk (X: Type) {wsX: Ws X} {vrX: Vr X} {wkX: Wk X} :=
    {wsiWk: ∀ (δ: Dom) (x: X), ⟨ S δ ⊢ wk x ⟩ → ⟨ δ ⊢ x ⟩}.
  Class WsAp (X Y: Type) {vrY: Vr Y} {ap: Ap X Y} {wsX: Ws X} {wsY: Ws Y} :=
    {wsAp: ∀ {ξ γ δ x}, ⟨ ξ : γ => δ ⟩ → ⟨ γ ⊢ x ⟩ → ⟨ δ ⊢ x[ξ] ⟩}.
  Class WsLift (X Y: Type) {vrX: Vr X} {vrY: Vr Y} {liftXY: Lift X Y} {wsX: Ws X} {wsY: Ws Y} :=
    {wsTm: ∀ (δ: Dom) (x: X), ⟨ δ ⊢ x ⟩ → ⟨ δ ⊢ lift x ⟩}.

End Unused.


Create HintDb ws.

Hint Constructors wsIx : ws.

Ltac crushRewriteH :=
  autorewrite with infrastructure in *.
Ltac crushRewrite2H :=
  autorewrite with infrastructure2 in *.

Ltac crushDbMatchH :=
  match goal with
    | [ H: S _                  = S _                  |- _ ] => apply eq_add_S in H
    | [ H: @vr ?X ?vrX _        = @vr ?X ?vrX _        |- _ ] => eapply vr_inj in H; eauto
    | [ H: @wk ?X ?vrX ?wkX _   = @wk ?X ?vrX ?wkX _   |- _ ] => eapply wk_inj in H; eauto
    | [ H: @lift ?X ?Y ?liftX _ = @lift ?X ?Y ?liftX _ |- _ ] => eapply lift_inj in H; eauto

    | [ |- S _                  = S _                  ] => f_equal
    | [ |- @vr ?X ?vrX _        = @vr ?X ?vrX _        ] => apply (f_equal (@vr X vrX))
    | [ |- @wk ?X ?vrX ?wkX _   = @wk ?X ?vrX ?wkX _   ] => apply (f_equal (@wk X vrX wkX))
    | [ |- @lift ?X ?Y ?liftX _ = @lift ?X ?Y ?liftX _ ] => apply (f_equal (@lift X Y liftX))
  end.

Ltac crushDb :=
  intros;
  repeat
    (repeat
       (crushRewriteH;
        repeat crushDbMatchH;
        cbn in *
       );
     try discriminate; eauto;
     crushRewrite2H
    ).
