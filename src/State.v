(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Export Arith Arith.EqNat.
Require Import Id.
Require Import Coq.Program.Equality.

Section S.

  Variable A : Set.
  
  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).
  
  (* Functional version of binding-in-a-state relation *)
  Fixpoint st_eval (st : state) (x : id) : option A :=
    match st with
    | (x', a) :: st' =>
        if id_eq_dec x' x then Some a else st_eval st' x
    | [] => None
    end.

  Lemma state_deterministic' (st : state) (x : id) (n m : option A)
    (SN : st_eval st x = n)
    (SM : st_eval st x = m) :
    n = m.
  Proof.
    congruence.
  Qed.
  
  Lemma state_deterministic (st : state) (x : id) (n m : A)   
    (SN : st / x => n)
    (SM : st / x => m) :
    n = m. 
  Proof.
    induction SN.
    - inversion SM; subst.
      + reflexivity.
      + congruence.
    - inversion SM; subst.
      + congruence.
      + apply IHSN. assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update. constructor.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    unfold update. split; intros H.
    - apply st_binds_tl.
      + apply neq_id_sym. assumption.
      + assumption.
    - inversion H; subst.
      + congruence.
      + assumption.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    unfold update. split; intros H.
    - inversion H as [ | ? ? ? ? ? H_neq H_bind ]; subst.
      + constructor.
      + inversion H_bind as [ | ? ? ? ? ? H_neq2 H_bind2 ]; subst.
        * congruence.
        * apply st_binds_tl; assumption.
    - inversion H as [ | ? ? ? ? ? H_neq H_bind ]; subst.
      + constructor.
      + apply st_binds_tl.
        * assumption.
        * apply st_binds_tl; assumption.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [Heq | Hneq].
    - subst x2.
      assert (n1 = m) by (eapply state_deterministic; eassumption).
      subst m.
      apply update_eq.
    - apply st_binds_tl; [congruence | assumption].
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    unfold update in *.
    inversion SM as [ | ? ? ? ? ? H_neq H_bind ]; subst.
    - apply st_binds_tl; [apply neq_id_sym; assumption | constructor].
    - inversion H_bind as [ | ? ? ? ? ? H_neq2 H_bind2 ]; subst.
      + constructor.
      + apply st_binds_tl; [assumption | apply st_binds_tl; [assumption | assumption]].
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    intros x a. tauto.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    intros x a.
    specialize (H x a).
    tauto.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    intros x a.
    specialize (H1 x a).
    specialize (H2 x a).
    tauto.
  Qed. 

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    subst. apply st_equiv_refl.
  Qed.

End S.