From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
Import MCMonadNotation.

(** * Auxiliaries *)

(** Substitute [s] for subterm [t] in term [T]. *)
Ltac subst_pattern T t s :=
  match eval pattern t in T with
  | ?f _ => let T' := eval cbv beta in (f s) in T'
  end.

(** Copied from [stdpp]. *)
Ltac get_head e :=
  lazymatch e with
  | ?h _ => get_head h
  | _ => e
  end.

(** Get the conclusion head of a type [T]. If [T] is [forall a, forall b, ..., h x y z],
then [concl_head T] returns [h]. *)
Ltac concl_head T :=
  let rec go T :=
    lazymatch T with
    | forall X, @?T X =>
        let T := open_constr:(T _) in
        let T := eval hnf in T in
        go T
    | _ => get_head T
    end
  in go T.

(** * Utilities for MetaCoq *)

(** Get the list of constructors of an inductive type. The constructor name is
converted to Coq builtin [string] type, so the users are not exposed to MetaCoq
internals. *)
Definition get_ctors (tm : term)
  : TemplateMonad (list (String.string * typed_term)) :=
  match tm with
  | tInd ind _ =>
     mind <- tmQuoteInductive ind.(inductive_mind);;
     match nth_error mind.(ind_bodies) ind.(inductive_ind) with
     | Some body =>
         monad_map_i (fun i cstr =>
                        tm <- tmUnquote (tConstruct ind i []);;
                        ret (String.to_string (cstr_name cstr), tm))
                     body.(ind_ctors)
     | _ => tmFail "No body found"
     end
  | _ => tmFail "Not an inductive type"
  end.

(* Copied from MetaCoq's [add_constructor] example. *)
Fixpoint try_remove_n_lambdas (n : nat) (t : term) {struct n} : term :=
  match n, t with
  | 0, _ => t
  | S n, tLambda _ _ t => try_remove_n_lambdas n t
  | S _, _ => t
  end.

Definition remove_last_n {A} (l : list A) (n : nat) : list A :=
  firstn (#|l| - n) l.

Definition new_cstr mdecl (idc : ident) (ctor : term) : constructor_body :=
  let '(args, concl) := decompose_prod_assum [] ctor in
  let (hd, indices) := decompose_app concl in
  {| cstr_name := idc;
    cstr_args := remove_last_n args #|mdecl.(ind_params)|;
    cstr_indices := skipn mdecl.(ind_npars) indices;
    cstr_type := ctor;
    cstr_arity := context_assumptions args |}.


(** * Inductive Definition Transformers *)

(** Mutual inductive definitions are not supported yet. *)

(** The type returned by the constructor transformer tactics. *)
Notation tsf_ctors_ty T := (list (String.string * (False -> T -> Type))).

(** Used by constructor transformers to remove cases. *)
Inductive tsf_skip_marker : Prop.
Ltac tsf_skip := exact tsf_skip_marker.

(** Transform a list of constructors to the target ones. [ind] is the inductive
type being transformed, [tsf_ident] is the name transformer function, and
[tsf_ctor] is the constructor transformer tactic. [tsf_ctor] takes as arguments
the constructor being transformed and the relation being defined. *)
Tactic Notation "tsf_ctors" constr(ind) open_constr(tsf_ident) tactic3(tsf_ctor) :=
  let tm := constr:(<% ind %>) in
  run_template_program (get_ctors tm)
    (fun xs =>
       let xs := eval simpl in xs in
       let rec go xs :=
         lazymatch xs with
         | (?name, (existT_typed_term _ ?ctor)) :: ?xs =>
             let n := eval compute in (tsf_ident name) in
             refine ((n, _) :: _); [
               intros Hc R; tsf_ctor ctor R
             | go xs ]
         | _ => exact []
         end
       in go xs).

Ltac tsf_ctor_id_ ind ctor R :=
  let T := type of ctor in
  let P := subst_pattern T ind R in
  exact P.

Ltac tsf_ctor_id ctor R :=
  let T := type of ctor in
  let ind := concl_head T in
  tsf_ctor_id_ ind ctor R.

(** An "identity" constructors transformer. *)
Tactic Notation "tsf_ctors_id" constr(ind) := tsf_ctors ind id (tsf_ctor_id_ ind).

(** This tactic does some post-processing to the list of target constructors. It
removes all skipped cases and quotes the constructor types. *)
Ltac tsf_ctors_to_tm ctors :=
  let rec go xs :=
    lazymatch xs with
    | (?n, ?ctor) :: ?xs =>
        lazymatch ctor with
        | (fun _ => ?P) =>
            lazymatch P with
            | (fun _ => tsf_skip_marker) => idtac
            | _ => quote_term P (fun P => refine ((n, P) :: _))
            end
        end; go xs
    | _ => refine ([])
    end in
  (* Not ideal. If parts of [ctors] are defined as definitions, we need to
  use [Arguments] to instruct [cbn] to unfold those definitions. *)
  let xs := eval cbn in ctors
    in go xs.

(** Allow for interactively developing constructor transformers in proof mode. *)
Ltac tsf_interact c _ := pose c as ctor.

(** The same as [False_rect] but more convenient for pattern matching. *)
Definition any {T} (Hc : False) : T := False_rect T Hc.
Opaque any.
Notation Any := (any _).

Ltac specialize_any H := specialize (H (any ltac:(assumption))).

(** Some type class magic for convenient user interface. *)

Definition QuoteTermOf {T : Type} (t : T) := term.
Existing Class QuoteTermOf.
#[export]
Hint Extern 1 (QuoteTermOf ?t) => quote_term t (fun t => exact t) : typeclass_instances.

Definition CtorTermsOf {T : Type} (cs : tsf_ctors_ty T) :=
  list (String.string * term).
Existing Class CtorTermsOf.
#[export]
Hint Extern 1 (CtorTermsOf ?cs) => tsf_ctors_to_tm cs : typeclass_instances.

Definition TypeOf {T : Type} (t : T) := Type.
Existing Class TypeOf.
#[export]
Hint Extern 1 (@TypeOf ?T _) => exact T : typeclass_instances.

Notation type_of t := (_ : TypeOf t) (only parsing).

(** Generate inductive definitions. [ind_gen] takes the name of the generated
definition, the list of its (quoted) constructors, and the "meta-information"
required by MetaCoq. *)
#[universes(polymorphic)]
Definition ind_gen (name : String.string) (ctors : list (String.string * term))
           (mind : mutual_inductive_body) (i : nat) : TemplateMonad unit :=
  let ctors := map (fun '(n, t) =>
                      new_cstr
                        mind (String.of_string n)
                        (* We do not support mutual inductive type. *)
                        (try_remove_n_lambdas 1 t)) ctors in
  match nth_error mind.(ind_bodies) i with
  | Some ind =>
      let ind' :=
        {| ind_finite := mind.(ind_finite);
           ind_npars := mind.(ind_npars);
           ind_universes := mind.(ind_universes);
           ind_variance := mind.(ind_variance);
           ind_params := mind.(ind_params);
           ind_bodies := [ {| ind_name := String.of_string name;
                              ind_indices := ind.(ind_indices);
                              ind_sort  := ind.(ind_sort);
                              ind_type  := ind.(ind_type);
                              ind_kelim := ind.(ind_kelim);
                              ind_ctors := ctors;
                              ind_projs := ind.(ind_projs);
                              ind_relevance := ind.(ind_relevance) |} ]
        |}
      in tmMkInductive' ind'
  | _ => tmFail "No body found"
  end.

(** Default meta-information for inductive definition. *)
Definition tsf_default_mind (ty : term) : mutual_inductive_body * nat :=
  ({| ind_finite := Finite;
      ind_npars := 0;
      ind_params := [];
      ind_universes := Monomorphic_ctx;
      ind_variance := None;
      ind_bodies := [ {|
         ind_name := "";
         (* Technically, [ind_indices] should be computed from [ty] (by
         [decompose_prod_assum]), but it seems Coq will automatically fix it. *)
         ind_indices := [];
         ind_sort := Sort.of_levels (inl PropLevel.lProp);
         ind_type := ty;
         ind_kelim := IntoPropSProp;
         ind_ctors := [];
         ind_projs := [];
         ind_relevance := Relevant |} ] |}, 0).

(** Generate an inductive definition of type [T] and constructors [cs]. [ty] is
needed to get around some universe inconsistency issues. *)
Definition tsf_ind_gen (T : Type) (name : String.string) (cs : tsf_ctors_ty T)
           `{ty : @QuoteTermOf _ T}
           `{ctors : @CtorTermsOf _ cs}
  : TemplateMonad unit :=
  let (mind, i) := tsf_default_mind ty in
  ind_gen name ctors mind i.

(** Get the meta-information of the (quoted) type [ty]. *)
Definition tsf_get_mind (ty : term)
  : TemplateMonad (mutual_inductive_body * nat) :=
  match ty with
  | tInd ind _ =>
     mind <- tmQuoteInductive ind.(inductive_mind);;
     ret (mind, ind.(inductive_ind))
  | _ => tmFail "Not an inductive type"
  end.

(** Generate an inductive definition that has the same meta-information as [t]
with constructors [cs]. *)
Definition tsf_ind_gen_from {T : Type} (t : T) (name : String.string)
           (cs : tsf_ctors_ty T)
           `{ty : @QuoteTermOf _ t}
           `{ctors : @CtorTermsOf _ cs}
  : TemplateMonad unit :=
  '(mind, i) <- tsf_get_mind ty;; ind_gen name ctors mind i.

(** This bidirectional hint is crucial if we want to use [app] to concatenate
transformed constructor lists. Otherwise, Coq would be too dumb to propagate the
type information to the constructor transformer tactics. *)
Arguments app _ & _ _.
