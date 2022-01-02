From idt Require Import idt.
From Coq Require Import Relations.Relation_Operators.
From Coq Require Import String.
Open Scope string_scope.

(** We will be using this simply typed lambda calculus example, adapted from
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

(** This small-step relation is more permissive and nondeterministic. *)
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

(** Let's say we want to have a bunch of lemmas about [multistep], each
corresponds to a case in [step]. For example, *)
Lemma multistep_app2 v1 t2 t2' :
  t2 ==>* t2' ->
  tapp v1 t2 ==>* tapp v1 t2'.
Proof.
  induction 1.
  - apply rt1n_refl.
  - eapply rt1n_trans; eauto using step.
Qed.

(** It is not hard to state and prove these lemmas by hand. But we need to write
one for each case of [step]. This could result in a lot of boilerplate codes
when we are dealing with a more complex language. If we grow the language later,
we also need to add more lemmas and fix the existing ones.

What we are going to do now is to generate these boilerplate lemmas as an
inductive definition [mstep]: each case of [mstep] corresponds to one of these
lemmas. For example, one constructor of [mstep], say [MST_App2], should has
type: [forall v1 t2 t2', t2 ==>* t2' -> mstep (tapp v1 t2) (tapp v1 t2')]. Once we
have proved [mstep] implies [multistep], whenever we need one of these lemmas,
we can simply apply this fact and the corresponding constructor.

Using IDT, We can generate them by: *)
(**
[[
MetaCoq Run (tsf_ind_gen_from
               step "mstep"
               ltac:(tsf_ctors step (append "M") tsf_step)).
]]
where [tsf_step] is a key tactic we are about to write.
*)
(** Let's unfold this command. [tsf_ind_gen_from], defined in the IDT library,
generates a new inductive definition [mstep] with the same type and other
"meta-information" from [step]. [tsf_ctors] is the main tactic that generates
the constructors of [mstep] from the constructors of [step], according to a name
transformer and a user-provided constructor transformer tactic [tsf_step].
[tsf_step] takes two arguments: the constructor from [step] being transformed,
and the relation being defined (i.e. [mstep]). It should build the type of the
target constructor. The easiest way to implement this tactic is probably to do
it interactively in proof mode. *)
Definition mstep_ctors : tsf_ctors_ty (type_of step).
Proof.
  (** This definition's type is the type of the third argument to
  [tsf_ind_gen_from], i.e. the [ltac:(...)] part. We run the tactic [tsf_ctors]
  with the constructor transformer tactic [tsf_interact], which does nothing but
  poses its two arguments to the hypothesis context. *)
  tsf_ctors step (append "M") tsf_interact.

  (** It generates 6 subgoals, each corresponds to a case in [step]. Let's focus
  on the case of [ST_App2] as an example. *)
  3 : {
    (** Now we can try to implement [tsf_step]. The two arguments to [tsf_step]
    are available in the context. [ctor] is the constructor from [step] being
    transformed: in this case it is [ST_App2]. [R] is the relation we try to
    generate. We may rename it to [mstep] to make it clearer. *)
    rename R into mstep.
    (** There is also a proof of [False] in the context that will come in handy
    later. *)

    (** Our goal here is to build the type of the corresponding constructor in
    [mstep], i.e. the type of [MST_App2]. In this case, it is: *)
    exact (forall v1 t2 t2' : tm, t2 ==>* t2' -> mstep (tapp v1 t2) (tapp v1 t2')).
    (** But of course we want to build this type in a more general way, so that
    other cases are also handled. *)
    Undo.
    (** Our strategy is to analyze the type of [ctor] and apply [refine]
    accordingly. Here we want to replace [step] with [multistep] in the
    conditions and with [mstep] in the conclusion, while keeping other parts of
    the type unchanged. First, let's use a shorter name. You can keep [ctor] if
    you want though. *)
    pose proof ctor as H.
    (** If the type starts with an universal quantifier, we simply keep it. We
    need to let Coq know this is a [Prop] or it will complains about universal
    inconsistency. *)
    match type of H with
    | forall x : ?T, _ => refine (forall x : T, _ : Prop)
    end.
    (** To continue, we need to get rid of the first unversal quantifier that we
    just done dealing with. We simply instantiate it with the one introduced by
    [refine]. *)
    specialize (H v1).
    (** To do it properly. *)
    Undo 2.
    match type of H with
    | forall x : ?T, _ => refine (forall x : T, _ : Prop); specialize (H x)
    end.

    (** There are two more to go. Be carefule to not consume too many, because
    [forall x : ?T, _] also matches the non-dependent arrow [_ -> _]. *)
    do 2
    match type of H with
    | forall x : ?T, _ => refine (forall x : T, _ : Prop); specialize (H x)
    end.

    (** Now if the premise is a [step], we replace it with [multistep]. *)
    match type of H with
    | (?t ==> ?t') -> ?T' => refine (t ==>* t' -> _ : Prop)
    end.
    (** This script works in this case. But for a more complicated relation,
    [step] may be only part of the premise, e.g., the type may have the form
    [(... -> _ ==> _) -> _]. In our experience, the best practice is to replace
    it using [pattern]: *)
    Undo.
    match type of H with
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
    match type of H with
    | ?T -> ?T' => let P := subst_pattern T step multistep in
                   refine (P -> _ : Prop)
    end.
    (** But now how do we get rid of the premise [t2 ==> t2'] to continue? We
    can simply discharge it with the proof of [False]! *)
    specialize (H ltac:(contradiction)).
    (** There is also a tactic for that in IDT, called [specialize_any]. Let's
    handle this premise again. *)
    Undo 2.
    match type of H with
    | ?T -> ?T' => let P := subst_pattern T step multistep in
                   refine (P -> _ : Prop); specialize_any H
    end.
    (** The conclusion is the only thing left. We replace [step] with [mstep]. *)
    match type of H with
    | ?t ==> ?t' => exact (mstep t t')
    end.
  }

  (** Let's put everything together. We use [ST_App1] as an example this time. *)
  2 : {
    rename R into mstep.
    pose proof ctor as H.
    (** We repeatedly pattern match the type of [H] and [refine] accordingly,
    like how we did it before. We need to put [?T -> ?T'] above [forall x : ?T, _]
    because the latter also matches non-dependent arrows. *)
    repeat
      match type of H with
      | ?T -> ?T' => let P := subst_pattern T step multistep in
                     refine (P -> _ : Prop); specialize_any H
      | forall x : ?T, _ => refine (forall x : T, _ : Prop); specialize (H x)
      | ?t ==> ?t' => exact (mstep t t')
      end.
  }

  (** We can do that for all other cases too. *)
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

(** Now let's print out this definition and see if the constructors we just built
look good. *)
Eval unfold mstep_ctors in mstep_ctors.

(** We can technically use this definition directly in the [tsf_gen_ind_from]
call, though we need to tell Coq to unfold it automatically.
[[
Arguments mstep_ctors /.
MetaCoq Run (tsf_ind_gen_from
               step "mstep"
               mstep_ctors).
]]
*)

(** However, we believe the better engineering practice is to extract what we
have developed into a tactic. This way it is more readable, easier for
maintenance and more resilient to future changes of the [step] relation. *)
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

(** At the moment, [mstep] is merely an inductive definition. To use it as
"lemmas" in backward reasoning, we have to prove [mstep] implies [multistep],
i.e. a "soundness" theorem. *)
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
Goal forall v1 t2 t2',
    t2 ==>* t2' ->
    tapp v1 t2 ==>* tapp v1 t2'.
  intros.
  apply mstep_sound.
  apply MST_App2.
  assumption.
  (** Or a one-liner. *)
  Undo 3.
  eauto using mstep_sound, mstep.
Qed.

(** Since [mstep] is an inductive definition, we can also add all constructors
to a hint database and further streamline the proof experience. *)
#[export]
Hint Resolve mstep_sound : mstep.
#[export]
Hint Constructors mstep : mstep.

Goal forall v1 t2 t2',
    t2 ==>* t2' ->
    tapp v1 t2 ==>* tapp v1 t2'.
  eauto with mstep.
Qed.

(** This example illustrates how we can generate boilerplate lemmas for backward
reasoning. We can also generate lemmas for forward reasoning, e.g., inversion
lemmas, and generate inductive types. For more realistic examples, see
_README.md_. *)
