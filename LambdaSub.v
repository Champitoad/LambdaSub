Require Import List String Rewriting.
Import ListNotations.
Open Scope string_scope.

Ltac inv H := inversion H; subst; clear H; try congruence.
Ltac econs := econstructor; eauto; try congruence.

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

(** Canonical example of typing for [f] in [t22]. *)

Example τf := ({"ℓ₁" : nat; "ℓ₂" : nat} → {"ℓ₃" : nat})%types.

Ltac wf :=
  match goal with
  |- well_formed ?Γ => intros a a' **; firstorder; destruct a, a'; congruence
  | _ => idtac
  end.

Example t22_typing : ⊢ (t22 τf) : τf → nat.
Proof.
  unfold t22. eapply (Abs [] []). simpl.
  econs.
  * eapply succ_typing.
  * econs.
    - econs.
      + econs.
        ** wf.
        ** econs. econs.
      + econs. firstorder.
        ** exists nat. econs.
           -- econs.
           -- inv H. econs. wf.
        ** exists nat. econs.
           -- right. econs.
           -- inv H. econs. wf.
    - econs.
Qed.

(** *** ----- WARNING -----

        What was initially a simple attempt at justifying an answer, turned into a quite long
        philosophical rambling about the fundamental nature of typing.
        
        The trace of this reflection has been left in this document, as of potential interest for
        the reader. But by no mean should the reader feel obliged to read it, not to mention
        interpret it as an expression of the beliefs of the author.
        
        Highly experimental work ahead! #</br># *)

(* begin hide *)
(* end hide *)

(** In all generality, one might describe the set of types ascribable to a term [t] as all
    _supertypes_ of some minimal, maximally refined type [τ₀]. Formally, we have:
    - [⊢ t : τ₀]
    - [forall τ, ⊢ t : τ -> τ₀ <: τ]
    The intuitive statement that [τf] is canonical can then be reformulated as an instance of the
    second proposition:
    - [forall τ, ⊢ (t22 τf) : τ -> (τf → nat) <: τ]
    This property should derive from the definition of [<:], which can be induced empirically by
    analysing the process of coming up with the idea that [τf] is canonical.
    
    So how did we infer the type [τf] of [f] in [t22]? One way to see it is that we executed
    mentally (and unconsciously) some _type inference algorithm_, with [t22] as input. But this
    presupposes that we already had the rules for [<:] present somewhere in our mind, and does not
    explain where they come from, nor how we came up with them!
    
    A more fundamental way of viewing the problem is by thinking of the type of a term as its
    meaning, and of _meaning as usage_ (in a Wittgensteinian tradition). The question is thus: how
    is [f] _used_ inside of [t22]? By looking at the _context_ surrounding its (only) occurrence, we
    first see that it is applied to a record containing exactly 2 fields [ℓ₁] and [ℓ₂] of type
    [nat]. This informs us of at least two things:
    - since it is _applied_, [f] must be a function, and thus of an arrow type [?τ → ?τ']
    - the type [?τ] of its argument must be a _record_ type
    For the moment nothing new, this is just familiar type inference through unification. Now the
    most straightforward choice for [?τ] would be [{ℓ₁ : nat; ℓ₂ : nat}], in that it matches
    directly the shape of the argument. But as soon as we start thinking not only about how [f] _is
    used_ in the context of this application, but also about how it _might use_ its argument, it
    appears that allowing only this type for [?τ] would be too much of a restriction. Indeed, what
    if [f] uses only the field [ℓ₁]? Then it might take as argument as well records that contain
    only the [ℓ₁] field; and the same reasoning applies for [ℓ₂], or even the empty record if [f]
    never uses its argument. But we cannot _allow_ any record type that contains fields other than
    [ℓ₁] and [ℓ₂] with type [nat], because even if _not all_ functions with such input types use
    some other field than [ℓ₁] and [ℓ₂], or use [ℓ₁] or [ℓ₂] as something else than a natural
    number, _some_ of these functions do, and we want to _forbid_ them, because they would not work
    properly with the argument provided to them in [t22].
    
    In fact, the identification of [{ℓ₁ : nat; ℓ₂ : nat}] as a natural candidate also used
    implicitly the kind of reasoning we have just outlined. Indeed, the type that really matches
    directly the shape of the argument is... the argument itself! But since singletons of terms do
    not pertain to the language of types, we immediately recognized the field values as natural
    numbers. And again, this process of recognition can be seen in two ways: the _technical_ one,
    where numeral notation is parsed with a formal grammar (which highlights how the concept of type
    might collapse with that of formal language); and the _conceptual_ one, which imagines how [f] might use
    such field values. Here it gets a little more difficult to think about all the ways a natural
    number may be used, in contrast with records which intuitively can only be projected on their
    fields. The key is to think of the most direct way to use it; that is, what is the primitive
    operation on natural numbers? Ironically, the insight comes from... type theory itself
    (Martin-Löf's one), where the elimination rule for natural numbers builds a _recursor_. So if we
    consider e.g. [31], we would like to allow any other term which does not offer any usage that is
    not already possible with [31], in the same way that we allowed as argument of [f] any term
    which cannot be projected on something else than [ℓ₁] and [ℓ₂], viewed as natural numbers. This
    leads us to consider all other natural numbers, since the recursor works the same for all
    natural numbers. But one might consider a generalization of natural numbers as an instance of
    inductive construction, as is done in the Calculus of Inductive Constructions: in this case, it
    is possible to build a recursor (pattern-matching operator) that works the same _for all
    inductive types_. Following our previous argument, should we then allow any term of an inductive
    type for [ℓ₁] and [ℓ₂], rather than just natural numbers? It seems like we must impose an
    arbitrary distinction between "ways" to use a term, if we want to have a subtyping relation that
    does not make the type system trivial by allowing to ascribe any (inductive) type to a term. And
    this distinction is precisely the purpose of having different _names_ for types, and
    notations/constructors for terms of these types. So in the end, the numeral notation _does
    matter_ if we want a middle ground between an _unusable_, too _conservative_ type system that
    _distinguishes_ all terms, thus _forbidding_ any kind of common usage; and a _useless_, too
    _liberal_ type system that _identifies_ all terms (which is equivalent to a term system that
    identifies all types/usages, in the previously mentionned form of a unique eliminator), thus
    _allowing_ every kind of common usage (including wrong ones).

    This philosophical analysis allows us to better understand the motivation of some design choices
    in already existing type systems. Coq is an interesting example, as it claims to be very
    expressive (liberal), while staying strongly consistent (conservative), which is necessary for
    the purpose of formalizing all of mathematics. Such a tradeoff implies that most
    automation/usability features will always be compensated by some manual work imposed to the user
    in another part of the system, sometimes leaving to her the responsibilty of not breaking
    consistency. For example, even though Coq has a general induction mechanism, it must be
    reinstanciated for each inductive type, the latter having to be completely declared, specified
    and _named_ by the user. This can be justified by the aforementioned necessity to keep a
    distinction between eliminators, so that there is no ambiguity in the possible usages of an
    expression. Also, even if inductive constructors and custom notations give a powerful mean of
    building concisely a great variety of terms, each term will in the end have a unique typing.
    This is again caused by the great generality of dependent inductive types, which by the unity of
    their form, need to be discriminated arbitrarily and systematically by _names_. Then the
    subtyping/coercion mechanism can only be as arbitrary as these names, and therefore its
    specification is left to the user, with here the additional risk of breaking consistency (since
    there is no way to decide its correctness in general). *)

(** ** Question 3 *)

Reserved Infix "<:" (at level 30).

Inductive subtype : type -> type -> Prop :=
| STop τ :
  τ <: ⊤
| SNat :
  nat <: nat
| SArr τ₁ τ₁' τ₂ τ₂':
  τ₂ <: τ₁ -> τ₁' <: τ₂' ->
  τ₁ → τ₁' <: τ₂ → τ₂'
| SRec fts fts' :
  List.Forall (fun ft => List.In ft fts) fts' ->
  Types.Rec fts <: Types.Rec fts'
where "τ <: τ'" := (subtype τ τ') : typing_scope.

(** ** Question 4 *)

Lemma subtype_refl : forall τ,
  τ <: τ.
Proof.
  induction τ; econs.
  now apply Forall_forall.
Qed. 

Lemma subtype_trans : forall τ' τ τ'',
  τ <: τ' -> τ' <: τ'' -> τ <: τ''.
Proof.
  induction τ'; intros * H H'; inv H; inv H'; econs.
  rewrite Forall_forall in *. auto.
Qed.
