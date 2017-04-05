(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

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

  Lemma state_deterministic: forall (st : state) (x : id) (n m : A),
    st / x => n -> st / x => m -> n = m.
  Proof.
    intros.
    induction st.
    { inversion H. }
    inversion H.
    { inversion H0. congruence. congruence. }
    { inversion H0. congruence. auto. }
  Qed.

  Lemma update_eq : forall (st : state) (x : id) (n : A),
    st [x <- n] / x => n.
  Proof.
    intros.
    apply st_binds_hd.
  Qed.

  Lemma update_neq : forall (st : state) (x2 x1 : id) (n m : A),
    x2 <> x1 -> st / x1 => m -> st [x2 <- n] / x1 => m.
  Proof.
    intros.
    apply st_binds_tl.
    { unfold not. intros. auto. }
    { apply H0. }
  Qed.

  Lemma update_shadow : forall (st : state) (x1 x2 : id) (n1 n2 m : A),
    st[x2 <- n1][x2 <- n2] / x1 => m -> st[x2 <- n2] / x1 => m.
  Proof.
    intros.
    inversion H.
    { apply update_eq. }
    { apply update_neq. { unfold not. intros. auto. }
      inversion H6.
      { exfalso. assert (x1=x2). auto. unfold not in H5. auto. }
      { auto. }
    }
  Qed.

  Lemma update_same : forall (st : state) (x1 x2 : id) (n1 m : A),
    st / x1 => n1 -> st / x2 => m -> st [x1 <- n1] / x2 => m.
  Proof.
    intros.
    remember (eq_id_dec x1 x2).
    inversion s.
    { assert (n1 = m).
      { rewrite H1 in H.
        remember (state_deterministic st x2 n1 m).
        auto.
      }
      rewrite H1.
      rewrite H2.
      apply update_eq.
    }
    { apply update_neq. assumption. assumption. }
  Qed.

  Lemma update_permute : forall (st : state) (x1 x2 x3 : id) (n1 n2 m : A),
    x2 <> x1 -> 
    st [x2 <- n1][x1 <- n2] / x3 => m ->
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    intros.
    remember (eq_id_dec x1 x3).
    remember (eq_id_dec x2 x3).
    inversion s.
    { inversion s0.
      { congruence. }
      { assert (n2 = m).
        { rewrite H1 in H0.
          remember (update_eq (st[x2<-n1]) x3 n2).
          apply state_deterministic with (st[x2<-n1][x3<-n2]) x3.
          assumption. assumption.
        }
        rewrite H1.
        apply update_neq.
        { assumption. }
        { rewrite H3. apply update_eq. }
      }
    }
    { inversion s0.
      { assert (n1 = m).
        { rewrite H2 in H0.
          remember (update_eq st x3 n1).
          apply (update_neq (st[x3<-n1]) x1 x3 n2 n1) in H1.
          apply state_deterministic with (st[x3<-n1][x1<-n2]) x3.
          assumption. assumption.
          apply update_eq.
        }
        rewrite H3.
        rewrite H2.
        apply update_eq.
      }
      { apply update_neq. assumption.
        apply update_neq. assumption.
        inversion H0.
        congruence.
        inversion H9.
        congruence.
        assumption.
      }
    }
  Qed.
End S.
