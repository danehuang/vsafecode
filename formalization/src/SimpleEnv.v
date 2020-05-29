(* Coq standard library imports *)
Require Import DecidableType.

(* Other library imports *)
Add LoadPath "../libs".
Add LoadPath "../libs/CompCert-Toolkit".
Require Import Coqlib.
Require Import Tactics.


Module Make(X:DecidableType).

  Definition t (A:Type) := list (X.t * A).
  Definition empty (A:Type) : t A := nil.

  Fixpoint find {A:Type} (x:X.t) (env:t A) : option A := 
    match env with 
      | nil => None
      | (y,v)::env' => if X.eq_dec x y then Some v else find x env'
    end.

  Definition add {A:Type} (x:X.t) (v:A) (env:t A) : t A :=
    (x,v)::env.

  (* add with replacement *)
  Fixpoint addR {A:Type} (x:X.t) (v:A) (env:t A) : t A :=
    match env with
      | nil => (x,v)::env
      | (y,v')::env' => if X.eq_dec x y then (x,v)::env' else (y,v')::(addR x v env')
    end.
  
  Lemma env_add_s : forall A env x y (v:A),
    X.eq x y ->
    find x (add x v env) = Some v.
  Proof.
    intros. unfold add; simpl. destruct X.eq_dec; crush.
  Qed.
  Hint Resolve env_add_s : env_db.

  Lemma env_add_o : forall A env x y (v:A),
    ~ X.eq x y ->
    find y (add x v env) = find y env.
  Proof.
    intros. unfold add; simpl. destruct X.eq_dec; crush.
  Qed.
  Hint Resolve env_add_o : env_db.

  Fixpoint dom {A:Type} (env:t A) : list X.t :=
    match env with
      | nil => nil
      | (x,_)::env' => x :: dom env'
    end.

End Make.
