Require Import List String Rewriting.
Import ListNotations.
Open Scope string_scope.

(** * Preliminary definitions *)

(** The denumerable sets for identifiers and labels will be that of arbitrary strings, for the sake
    of readability. *)

Definition ident := string.
Definition string_ident : string -> ident := fun x => x.
Coercion string_ident : string >-> ident.

Definition label := string.
Definition string_label : string -> label := fun x => x.
Coercion string_label : string >-> label.

(** Abstract syntax and notations for types. *)

Module Types.

Inductive type :=
| Top
| Nat
| Arr (τ τ' : type)
| Rec (fts : list field)
with field :=
| Fd (ℓ : label) (τ : type).

Hint Constructors type : db.

Declare Scope types_scope.
Delimit Scope types_scope with types.
Bind Scope types_scope with type.

Notation "⊤" := Top : types_scope.
Notation "'nat'" := Nat : types_scope.
Infix "→" := Arr (at level 1) : types_scope.
Notation "{}" := (Rec []) : types_scope.
Notation "{ x ; .. ; y }" := (Rec (cons x .. (cons y []) ..))
 (format "{ x ;  .. ;  y }") : types_scope.
Notation "ℓ  :  τ" := (Fd ℓ τ) (at level 10) : types_scope.

Open Scope types_scope.

Example rectangle := {"dimensions" : {"width" : nat; "height" : nat}; "color" : nat}.
Example foo := {"bar" : (nat → nat) → nat → rectangle; "baz" : {}}.

End Types.

(** Abstract syntax and notations for terms. *)

Module Terms.

Import Types.

Inductive term :=
| Var (x : ident)
| Nat (n : Datatypes.nat)
| App (t u : term)
| Abs (x : ident) (τ : type) (t : term)
| Rec (fds : list field)
| Acc (t : term) (ℓ : label)
with field :=
| Fd (ℓ : label) (t : term).

Hint Constructors term : db.

Declare Scope terms_scope.
Delimit Scope terms_scope with terms.
Bind Scope terms_scope with term.

Coercion Var : ident >-> term.
Coercion Nat : Datatypes.nat >-> term.

Notation "< t > u" := (App t u)
 (format "< t >  u", at level 30, t at level 40) : terms_scope.
Notation "'λ' ( x : τ ) t" := (Abs x τ t)
 (format "'λ' ( x  :  τ )  t", at level 40, x at level 0, t at level 40) : terms_scope.
Notation "{}" := (Rec []) : terms_scope.
Notation "{ x ; .. ; y }" := (Rec (cons x .. (cons y []) ..))
 (format "{ x ;  .. ;  y }") : terms_scope.
Notation "t · ℓ" := (Acc t ℓ)
 (format "t · ℓ", at level 10) : terms_scope.
Notation "ℓ  =  t" := (Fd ℓ t) : terms_scope.

Open Scope terms_scope.

Example rectangle := {"dimensions" = {"width" = 20; "height" = 10}; "color" = 255}.
Example foo := {"bar" = λ("f":nat→nat) λ("x":nat) rectangle}.
Example bar := <foo·"bar"> 42.

End Terms.

(** * Exercise 1 *)

(** ** Question 1 *)

(** Values are either variables, natural numbers, λ-abstractions, or records whose field "values"
    are themselves values. *)

Import Terms.

Definition get_label '(ℓ = _) := ℓ.
Definition get_value '(_ = t) := t.

Inductive value : term -> Prop :=
| value_var x : value (Var x)
| value_nat n : value (Nat n)
| value_abs x a t : value (Abs x a t)
| value_rec fds : List.Forall value (List.map get_value fds) -> value (Rec fds).

Hint Constructors value : db.

(** ** Question 2 *)

(** To implement the value restriction of left application contexts, we "hardcode" in the abstract
    syntax of contexts a proof of the [value] predicate defined in question 1. Since it lives in
    [Prop], it can be removed during extraction, and thus belongs strictly to the metatheoretical
    level. Therefore this approach would not scale to more complex developments, where the purpose
    is the extraction of a certified interpreter/compiler. *)

Module Contexts.

Inductive context :=
| Nil
| RApp (t : term) (C : context)
| LApp (C : context) (v : term) (p : value v)
| Rec (fd : field) (fds : list Terms.field)
| Acc (C : context) (ℓ : label)
with field :=
| Fd (ℓ : label) (C : context).

Hint Constructors context : db.

(** Some notations again to make proofs more readable. *)

Declare Scope contexts_scope.
Delimit Scope contexts_scope with contexts.
Bind Scope contexts_scope with context.

Notation "[]" := Nil : contexts_scope.
Notation "[]" := nil : list_scope. (* Redeclare list notation *)
Notation "< t > C" := (RApp t C)
 (format "< t >  C", at level 30, t at level 40, only printing) : contexts_scope.
Notation "< C > v { p }" := (LApp C v p)
 (format "< C >  v  { p }", at level 30, C at level 40, only printing) : contexts_scope.
Notation "{| x |}" := (Rec x []) : contexts_scope.
Notation "{| x ; y ; .. ; z |}" := (Rec x (cons y .. (cons z []) ..))
 (format "{| x ;  y ;  .. ;  z |}") : contexts_scope.
Notation "C · ℓ" := (Acc C ℓ)
 (format "C · ℓ", at level 10) : contexts_scope.
Notation "ℓ  =  C" := (Fd ℓ C) : contexts_scope.
Notation "t  =  u" := (eq t u) : core_scope. (* Redeclare eq notation *)

Open Scope contexts_scope.

Example rectangle :=
  {|"dimensions" = {|"width" = []; ("height" = 10)%terms|}; ("color" = 255)%terms|}.

End Contexts.

(** ** Question 3 *)

(** First, we need a function that tells us how to _fill_ a context. *)

Import Contexts.

Reserved Notation "C [ t ]" (at level 9, t at level 8).

Fixpoint fill_context C t :=
  match C with
  | [] => t
  | RApp u C => <u> C[t]
  | LApp C u _ => <C[t]> u
  | Rec (ℓ = C) fds => Terms.Rec ((ℓ = C[t]) :: fds)%terms
  | C·ℓ => (C[t]·ℓ)%terms
  end
where "C [ t ]" := (fill_context C t).

(** Next, we need a (capture-avoiding) _substitution_ function for β-reduction. *)

Close Scope contexts_scope.

Fixpoint freevars t :=
  match t with
  | Var y => [y]
  | Nat _ => []
  | <u> v => (freevars u ++ freevars v)%list
  | λ(x : _) u => List.remove string_dec x (freevars u)
  | Terms.Rec fds => List.flat_map (fun fd => freevars (get_value fd)) fds
  | t·ℓ => freevars t
  end.

Reserved Notation "t [ u / x ]" (at level 9, u at level 8).

Fixpoint subst t u x :=
  match t with
  | Var y => if x =? y then u else t
  | Nat _ => t
  | <v> w => <v[u/x]> w[u/x]
  | λ(y : τ) v =>
    if x =? y then t
    else if List.in_dec string_dec y (freevars u) then t
    else λ(y : τ) v[u/x]
  | Terms.Rec fds => Terms.Rec (List.map (fun '(ℓ = v) => (ℓ = v[u/x])) fds)
  | v·ℓ => v[u/x]
  end
where "t [ u / x ]" := (subst t u x) : terms_scope.

(** Finally, we can define reduction rules as an inductive predicate. To reduce the number of rules
    while exploiting earlier definitions using evaluation contexts, we split the predicate in two:
    - [reduce] implements _redex rewriting_ 
    - [step] extends [reduce] to arbitrary evaluation contexts, and thus also implements _redex
      search_ *)

Module Reductions.

Reserved Infix "~>" (at level 50).

Inductive reduce : term -> term -> Prop :=

| AppAbs x τ t v : value v ->
  <λ(x : τ) t> v ~> t[v/x]

| AccRec fds ℓ v : value v ->
  List.In (ℓ = v) fds ->
  (Terms.Rec fds)·ℓ ~> v
  
where "t ~> u" := (reduce t u).

Hint Constructors reduce : db.

Reserved Infix "-->" (at level 50).

Inductive step : term -> term -> Prop :=

| Ctx C t u :
  t ~> u ->
  C[t] --> C[u]

where "t --> u" := (step t u).

Hint Constructors step : db.

(** Some notations for the transitive closures of reductions that will be useful later. *)

Infix "~*>" := (multi reduce) (at level 50).
Infix "-*->" := (multi step) (at level 50).

Hint Constructors multi : db.

End Reductions.

(** ** Question 4 *)

Import Reductions.

Definition reducible t := exists u, t --> u.

Theorem step_redex :
  forall t, reducible t -> exists C u, eq t C[u].
Proof.
  destruct 1 as [? H]. destruct H. eauto.
Qed.

(** * Exercise 2 *)

(** ** Question 1 *)

Module Typing.

Export Types.

(** First we need typing contexts, with a well-formedness predicate [well_formed]. *)

Inductive assumption :=
| Assum (x : ident) (τ : type).

Hint Constructors assumption : db.

Definition context := list assumption.

Declare Scope typing_scope.
Delimit Scope typing_scope with typing.
Bind Scope typing_scope with assumption context.

Notation "x : τ" := (Assum x τ) : typing_scope.

Open Scope typing_scope.

Definition well_formed (Γ : context) :=
  forall a a', List.In a Γ -> List.In a' Γ ->
  let '(x : τ) := a in
  let '(x' : τ') := a' in
  x = x' -> τ = τ'.

(** Typing rules are implemented with the inductive predicate [well_typed]. *)

Reserved Notation "Γ ⊢ t : τ" (at level 10, t at level 0, τ at level 10).

Inductive well_typed : context -> term -> type -> Prop :=

| Var Γ x τ : well_formed Γ ->
  List.In (x : τ) Γ ->
  Γ ⊢ (Var x) : τ

| Nat Γ n : well_formed Γ ->
  Γ ⊢ (Terms.Nat n) : nat

| App Γ t u τ τ' :
  Γ ⊢ t : τ' → τ -> Γ ⊢ u : τ' ->
  Γ ⊢ (<t> u) : τ

| Abs Γ Γ' x t τ τ':
  (Γ ++ [x : τ] ++ Γ')%list ⊢ t : τ' ->
  (Γ ++ Γ')%list ⊢ (λ(x : τ) t) : τ → τ'

(** (Record) rule *)

| Rec Γ fds fts :
  (forall ℓ t, List.In (ℓ = t)%terms fds -> exists τ, List.In (ℓ : τ)%types fts /\ Γ ⊢ t : τ) ->
  Γ ⊢ (Terms.Rec fds) : Types.Rec fts

(** (Field) rule *)

| Acc Γ t ℓ τ fts :
  Γ ⊢ t : Rec fts -> List.In (ℓ : τ)%types fts ->
  Γ ⊢ (t·ℓ) : τ

where "Γ ⊢ t : τ" := (well_typed Γ t τ) : typing_scope.

Hint Constructors well_typed : db.

Notation "⊢ t : τ" := ([] ⊢ t : τ) (at level 10, t at level 0, τ at level 10).

End Typing.

(** ** Question 2 *)

Import Typing.

Axiom succ : term.
Axiom succ_typing : forall Γ, Γ ⊢ succ : nat → nat.

Definition t22 τ := λ("f" : τ) <succ> ((<"f"> {"ℓ₁" = 31; "ℓ₂" = 73})·"ℓ₃").

(** Canonical example of typing for [t22]. *)

Example τ22 := ({"ℓ₁" : nat; "ℓ₂" : nat} → {"ℓ₃" : nat})%types.

Example t22_typing : ⊢ (t22 τ22) : τ22 → nat.
Proof.
  unfold t22. eapply (Abs [] []). simpl.
  econstructor.
  * eapply succ_typing.
  * econstructor.
    - econstructor.
      + econstructor.
        ** unfold well_formed. firstorder.
           destruct a, a'. congruence.
        ** econstructor. econstructor.
      + econstructor. firstorder.
        ** exists nat. econstructor.
           -- econstructor. congruence.
           -- inversion H. econstructor.
              unfold well_formed. firstorder.
              destruct a, a'. congruence.
        ** exists nat. econstructor.
           -- right. econstructor. congruence.
           -- inversion H. econstructor.
              unfold well_formed. firstorder.
              destruct a, a'. congruence.
    - econstructor. congruence.
Qed.