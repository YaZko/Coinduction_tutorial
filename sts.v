CoInductive stream {A} : Type :=
| Cons (a : A) (s : stream) : stream
.

CoFixpoint ones := Cons 1 ones.
CoFixpoint twos := Cons 2 twos.

(* cofixes only reduce when they are the target of a match *)
Goal ones = ones.
  cbv.
  reflexivity.
Qed.
Goal match ones with
     | Cons a s => s
     end = ones.
  simpl.
  reflexivity.
Qed.

(* Not guarded *)
Fail CoFixpoint loop : stream nat := loop.

Fixpoint approx {A} n (s : stream) : list A :=
  match n with
  | O => nil
  | S n => match s with
          | Cons a s' => cons a (approx n s')
          end
  end.

Compute approx 10 ones.

CoFixpoint map {A B} (f : A -> B) (s : stream) : stream :=
  match s with
  | Cons a s' => Cons (f a) (map f s')
  end.

Compute approx 10 (map (fun x => x + 1) ones).

(* Not guarded (since this function may never finish) *)
Fail CoFixpoint filter {A} (p : A -> bool) (s : stream) : stream :=
  match s with
  | Cons a s' => if p a then Cons a (filter p s') else filter p s'
  end.
















Section SubjectReduction.
  CoInductive tick := Tick : tick -> tick.
  CoFixpoint loop := Tick loop.

  (* simply eq_refl is also a valid proof *)
  Definition etaeq : loop = loop :=
    match loop with
    | Tick t => eq_refl (Tick t)
    end.

  (* The dependent pattern match gives us some information (the
     definition of loop) about the structure of loop, and reducing the
     match loses this information, resulting in a different type *)
  Eval compute in etaeq.
  Fail Definition BOOM : loop = loop := Eval compute in etaeq.
End SubjectReduction.
























Require Import Paco.paco.

(** Example from "The Power of Parameterization in Coinductive Proof"

    a ---> b ---> c
         /^     ^ |
        //     /  |
       //     /   |
      v/     /    v
    d      e      f
*)

(* The finite type of Nodes: *)

Inductive Node: Type := a | b | c | d | e | f.

(* The edge relation *)
Inductive edge: Node -> Node -> Prop :=
| Sab: edge a b
| Sbc: edge b c
| Sbd: edge b d
| Sdb: edge d b
| Sec: edge e c
| Scf: edge c f
.
Hint Constructors edge.

(* We want to define the set of nodes from which it is possible to step indefinitely. (a, b, d)
   We have essentially three possibilities.
 *)

(* The positive coinductive style.
   Historical way of doing things in Coq
   Known to break subject reduction.
 *)
CoInductive inf : Node -> Prop :=
| step: forall x y, inf y -> edge x y -> inf x.

(* The negative coinductive style.
   Define first the functor, then define the coinductive
   as a coinductive record with primitive projections on
   to prevent pattern matching having a single field
   forcing the call to the functor.
   Think of it as: the primitive projection allows you
   to "observe" the outside call to the functor, that
   may in turn return a new state, i.e. a new object
   that you can observe.
 *)
Set Primitive Projections.
Inductive F (X: Node -> Prop): Node -> Prop :=
| Fstep: forall x y, X y -> edge x y -> F X x.
Hint Constructors F.

CoInductive inf' (x: Node) : Prop :=
  go { _observe : F inf' x}.

(* The paco way.
   While the two previous options stand both for
   coinductive types and coinductive predicates, paco
   is specific to coinductive predicates.
   It relies on the paco library to wrap Coq's syntactic
   guard checker into a semantic one based on a generalization
   of Tarski's theorem over a parameterized cofixed point.
 *)
Definition inf'' := paco1 F bot1.
Hint Unfold inf''.

(* We can now prove that a is the source of an infinite path.
   The normal way:
 *)
Lemma b_inf: inf b.
Proof.
  cofix CIH.
  apply step with d; auto.
  apply step with b; auto.
Qed.

Lemma a_inf: inf a.
Proof.
  apply step with b; auto.
  cofix CIH.
  apply step with d; auto.
  apply step with b; auto.
Qed.

(* The negative way: *)
Lemma a_inf': inf' a.
Proof.
  constructor.
  apply Fstep with b; auto.
  cofix CIH.
  constructor; apply Fstep with d; auto.
  constructor; apply Fstep with b; auto.
Qed.

(* The paco way: *)
Lemma a_inf'': inf'' a.
Proof.
  pfold.
  apply Fstep with b; auto.
  left.
  pcofix IHb.
  pfold.
  apply Fstep with d; auto.
  left.
  pfold.
  apply Fstep with b; auto.
Qed.

Lemma F_mon: monotone1 F.
Proof.
  pmonauto.
Qed.
Hint Resolve F_mon : paco.
