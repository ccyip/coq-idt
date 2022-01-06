From idt Require Import idt.
From Coq Require Import Relations.Relation_Operators.
From Coq Require Import String.
Open Scope string_scope.

(** We will be using a formalization of the simply typed lambda
    calculus as an example. This formalization is adapted from
    _Software Foundations_. *)

Inductive ty : Type :=
| TBool  : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tvar : string -> tm
| tapp : tm -> tm -> tm
| tabs : string -> ty -> tm -> tm
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if string_dec x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if string_dec x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue =>
      ttrue
  | tfalse =>
      tfalse
  | tif t1 t2 t3 =>
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Reserved Notation "t1 '==>' t2" (at level 40).

(** Our nondeterministic small-step reduction relation allows either
    the left or right subterm of an application to be reduced. *)
Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T t12 v2,
    (tapp (tabs x T t12) v2) ==> [x:=v2]t12
| ST_App1 : forall t1 t1' t2,
    t1 ==> t1' ->
    tapp t1 t2 ==> tapp t1' t2
| ST_App2 : forall v1 t2 t2',
    t2 ==> t2' ->
    tapp v1 t2 ==> tapp v1 t2'
| ST_IfTrue : forall t1 t2,
    (tif ttrue t1 t2) ==> t1
| ST_IfFalse : forall t1 t2,
    (tif tfalse t1 t2) ==> t2
| ST_If : forall t1 t1' t2 t3,
    t1 ==> t1' ->
    (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

(** The reflexive transitive closure of [step]. *)
Definition multistep := clos_refl_trans_1n _ step.
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 20).

(** Let's say we want to have a bunch of congruence lemmas about
    [multistep], each corresponding to a case in [step]. As one
    example: *)
Lemma multistep_app2 v1 t2 t2' :
  t2 ==>* t2' ->
  tapp v1 t2 ==>* tapp v1 t2'.
Proof.
  induction 1.
  - apply rt1n_refl.
  - eapply rt1n_trans; eauto using step.
Qed.

(** It is not hard to manually state and prove these lemmas, but we
    need to write one for each case of [step]. This can result in a
    lot of boilerplate statements when we are dealing with a more
    complex language. In addition, if we want to grow the language
    later, we will need to add more lemmas and fix the existing ones.

    What we are going to do instead is to encode each of these
    boilerplate lemmas as an inductive definition [mstep]: each case
    of [mstep] corresponds to one of these lemmas. For example, one
    constructor of [mstep], say [MST_App2], should has type: [forall
    v1 t2 t2', t2 ==>* t2' -> mstep (tapp v1 t2) (tapp v1 t2')]. Once
    we have proved [mstep] implies [multistep], whenever we need one
    of these lemmas, we can simply apply this fact and the
    corresponding constructor.

   Importantly using IDT, we can automatically generate this
   definition via the command: *)

(**
[[
MetaCoq Run (tsf_ind_gen_from step "mstep" mstep_ctors).
]]
*)

(** [tsf_ind_gen_from], defined in the IDT library, generates a new
    inductive definition named [mstep] with the same type and other
    "meta-information" from [step]. Its third argument to is a list of
    the signatures of the constructors of [mstep]. IDT provides
    several tactics to automatically generate this argument from the
    signatures of the constructors of [mstep] and the information
    provided by [step]. To see how these tactics work, it's helpful to
    first see how to interactively generate [mstep_ctors] in proof
    mode.*)

Definition mstep_ctors : tsf_ctors_ty (type_of step).
Proof.

  (** We use [tsf_ctors_ty] tactic to build the type of the
  constructor list[mstep_ctors]; IDT provides several tactics for
  generate such types.

  We begin by running the following tactic [tsf_ctors ]: *)

  tsf_ctors step (append "M'") tsf_interact.

(* [tsf_ctors] generates a subgoal one for each of the 6 constructor
   of [step], solving each goal "explains" how to build the type of a
   corresponding constructor. The second argument [tsf_ctors] is used
   to generate the names for each of these constructors. The final
   parameter is a tactic that is applied to each subgoal. This tactic
   takes two arguments: the constructor from [step] being transformed,
   and the relation being defined (i.e. [mstep]). In order to expose
   these arguments in the resulting subgoals, we use the constructor
   transformer tactic [tsf_interact], which does nothing but poses its
   two arguments to the hypothesis context. *)

  (** Let's focus on the case of [ST_App2] as an example of how an
  individual constructor is built. *)

  3 : {
    (** Now we can try to implement [tsf_step]. The two arguments to
    [tsf_step] are available in the context. [ctor] is the constructor
    from [step] being transformed: in this case it is [ST_App2]. [R]
    is the relation we try to generate. We may rename it to [mstep] to
    make it clearer. *)
    rename R into mstep.
    (** There is also a proof of [False] in the context that will come
    in handy later. *)

    (** Our goal here is to build the type of the corresponding
    constructor in [mstep], i.e. the type of [MST_App2]. In this case,
    it is: *)

    exact (forall v1 t2 t2' : tm, t2 ==>* t2' -> mstep (tapp v1 t2) (tapp v1 t2')).
    (** But of course we want to build this type in a more general way
    that can also handle other cases. *)
    Undo.
    (** Our strategy is to analyze the type of [ctor] and apply [refine]
    accordingly. Here we want to replace [step] with [multistep] in the
    conditions and with [mstep] in the conclusion, while keeping other parts of
    the type unchanged. *)

    (** If the type starts with an universal quantifier, we simply keep it. We
    need to let Coq know this is a [Prop] or it will complains about universal
    inconsistency. *)
    match type of ctor with
    | forall x : ?T, _ => refine (forall x : T, _ : Prop)
    end.
    (** To continue, we need to get rid of the first unversal quantifier that we
    just done dealing with. We simply instantiate it with the one introduced by
    [refine]. *)
    specialize (ctor v1).

    (** There are two more to go. We need to be careful to not consume
    too many, because [forall x : ?T, _] also matches the
    non-dependent arrow [_ -> _]. *)
    do 2
    match type of ctor with
    | forall x : ?T, _ => refine (forall x : T, _ : Prop); specialize (ctor x)
    end.

    (** Now if the premise is a [step], we replace it with [multistep]. *)
    match type of ctor with
    | (?t ==> ?t') -> ?T' => refine (t ==>* t' -> _ : Prop)
    end.
    (** This script works in this case. But for a more complicated relation,
    [step] may be only part of the premise, e.g., the type may have the form
    [(... -> _ ==> _) -> _]. In our experience, the best practice is to replace
    it using [pattern]: *)
    Undo.
    match type of ctor with
    | ?T -> ?T' =>
        match eval pattern step in T with
        | ?F _ => let P := eval cbv beta in (F multistep) in
                  refine (P -> _ : Prop)
        end
    end.
    (** This style has another benefit: it is a no-op if [step] does not appear
    in [T], so it naturally handles other boring cases. Because this practice is
    quite common, IDT provides a tactic to do the substitution. *)
    Undo.
    match type of ctor with
    | ?T -> ?T' => let P := subst_pattern T step multistep in
                   refine (P -> _ : Prop)
    end.
    (** But now how do we get rid of the premise [t2 ==> t2'] to continue? We
    can simply discharge it with the proof of [False]! *)
    specialize (ctor ltac:(contradiction)).
    (** There is also a tactic for that in IDT, called [specialize_any]. Let's
    handle this premise again. *)
    Undo 2.
    match type of ctor with
    | ?T -> ?T' => let P := subst_pattern T step multistep in
                   refine (P -> _ : Prop); specialize_any ctor
    end.
    (** The conclusion is the only thing left. We replace [step] with [mstep]. *)
    match type of ctor with
    | ?t ==> ?t' => exact (mstep t t')
    end.
  }

  (** Let's put everything together, using [ST_App1] as an example this time. *)
  2 : {
    rename R into mstep.
    (** We repeatedly pattern match the type of [ctor] and [refine] accordingly,
    like how we did it before. We need to put [?T -> ?T'] above [forall x : ?T, _]
    because the latter also matches non-dependent arrows. *)
    repeat
      match type of ctor with
      | ?T -> ?T' => let P := subst_pattern T step multistep in
                     refine (P -> _ : Prop); specialize_any ctor
      | forall x : ?T, _ => refine (forall x : T, _ : Prop); specialize (ctor x)
      | ?t ==> ?t' => exact (mstep t t')
      end.
  }

  (** This tactic discharges all the remaining cases as well. *)
  all:
    rename R into mstep;
    pose proof ctor as H;
    repeat
      match type of H with
      | ?T -> ?T' => let P := subst_pattern T step multistep in
                     refine (P -> _ : Prop); specialize_any H
      | forall x : ?T, _ => refine (forall x : T, _ : Prop); specialize (H x)
      | ?t ==> ?t' => exact (mstep t t')
      end.
Defined.

(** Now let's print out this definition and see if the constructors we
    just built look reasonable. *)
Eval unfold mstep_ctors in mstep_ctors.


(** We can technically use this definition directly in the [tsf_gen_ind_from]
call, though we need to tell Coq to unfold it automatically. *)

Arguments mstep_ctors /.
MetaCoq Run (tsf_ind_gen_from
               step "mstep'"
               mstep_ctors).

(** However, the better approach is to extract what we have developed
    into a tactic. This way it is more readable, easier for
    maintenance and more resilient to future changes of the [step]
    relation. *)
Ltac tsf_step ctor mstep :=
  let H := fresh in
  pose proof ctor as H;
  repeat
    match type of H with
    | ?T -> ?T' => let P := subst_pattern T step multistep in
                   refine (P -> _ : Prop); specialize_any H
    | forall x : ?T, _ => refine (forall x : T, _ : Prop); specialize (H x)
    | ?t ==> ?t' => exact (mstep t t')
    end.

MetaCoq Run (tsf_ind_gen_from
               step "mstep"
               ltac:(tsf_ctors step (append "M") tsf_step)).

Print mstep.

(** At the moment, [mstep] is merely an inductive definition. To use
    it as a set of "lemmas" in backward reasoning, we have to prove
    [mstep] implies [multistep], i.e. a "soundness" theorem. *)
Theorem mstep_sound t t' :
  mstep t t' ->
  t ==>* t'.
Proof.
  (** Each case we prove here corresponds to a proof of a lemma like
  [multistep_app2], and we can prove them all at once! *)
  destruct 1;
  try match goal with
      | H : _ ==>* _ |- _ => induction H
      end; unfold multistep;
    eauto using clos_refl_trans_1n, step.
Qed.

(** Now whenever we need a lemma about [multistep], we can reduce it to [mstep]
    and apply the corresponding constructor. *)
Example multistep_app2' : forall v1 t2 t2',
    t2 ==>* t2' ->
    tapp v1 t2 ==>* tapp v1 t2'.
Proof.
  intros.
  apply mstep_sound.
  apply MST_App2.
  assumption.
  (** Or a one-liner. *)
  Undo 3.
  eauto using mstep_sound, mstep.
Qed.

(** Since [mstep] is an inductive definition, we can also add all
    constructors to a hint database to further streamline the proof
    experience. *)
#[export]
Hint Resolve mstep_sound : mstep.
#[export]
Hint Constructors mstep : mstep.

Example multistep_app2'' : forall v1 t2 t2',
    t2 ==>* t2' ->
    tapp v1 t2 ==>* tapp v1 t2'.
Proof.
  eauto with mstep.
Qed.

(** This example illustrates how we can generate boilerplate lemmas
    for backward reasoning. We can also generate lemmas for forward
    reasoning, e.g., inversion lemmas, and generate inductive types. For
    more complicated examples, see _README.md_. *)
