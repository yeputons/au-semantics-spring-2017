(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).
Reserved Notation "m <<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) << (Id m)
where "n << m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).   

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).
Notation "n <<  m" := (lt_id n m).

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 << id2} + {id1 = id2} + {id2 << id1}.
Proof.
  intros id1 id2.
  destruct id1 as [n1].
  destruct id2 as [n2].
  assert (h: { n1 < n2 } + {n1 = n2} + {n2 < n1} ).
  { apply lt_eq_lt_dec. }
  inversion h.
  { inversion H.
    { left. left. apply lt_conv. apply H0. }
    { left. right. rewrite H0. reflexivity. }
  }
  { right. apply lt_conv. apply H. }
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof.
  intros id1 id2.
  destruct id1 as [n1].
  destruct id2 as [n2].
  assert (h: { n2 > n1 } + {n1 = n2} + {n1 > n2} ).
  { apply gt_eq_gt_dec. }
  inversion h.
  { inversion H.
    { right. apply gt_conv. apply H0. }
    { left. right. rewrite H0. reflexivity. }
  }
  { left. left. apply gt_conv. apply H. }
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof.
  intros id1 id2.
  destruct id1 as [n1].
  destruct id2 as [n2].
  assert (h: { n1 <= n2 } + {n1 > n2} ).
  { apply le_gt_dec. }
  inversion h.
  { left. apply le_conv. apply H. }
  { right. apply gt_conv. apply H. }
Qed.

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n1 n2.
  remember (lt_eq_lt_dec n1 n2).
  inversion s.
  { inversion H.
    { right. omega. }
    { left. omega. }
  }
  { right. omega. }
Qed.

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros. destruct id1 as [n1]. destruct id2 as [n2].
  remember (eq_dec n1 n2).
  inversion s.
  { left. rewrite H. reflexivity. }
  { right. unfold not. intros.
    assert (n1 = n2). { inversion H0. reflexivity. }
    contradiction.
  }
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p. 
Proof.
  intros.
  destruct (eq_id_dec x x).
  { reflexivity. }
  { exfalso. auto. (* contradiction *) }
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q. 
Proof.
  intros.
  destruct (eq_id_dec x y).
  { contradiction. }
  { reflexivity. }
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id, id1 >> id2 -> id2 >> id1 -> False.
Proof.
  intros. destruct id1. destruct id2.
  inversion H.
  inversion H0.
  omega.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id, id2 <<= id1 -> id2 >> id1 -> False.
Proof.
  intros. destruct id1. destruct id2.
  inversion H. inversion H0.
  omega.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof.
  intros. destruct id1. destruct id2.
  assert (n <= n0). { inversion H. auto. }
  apply le_lt_eq_dec in H0.
  inversion H0.
  { assert (n0 > n). { omega. } right. apply gt_conv. auto. }
  { left. rewrite H1. auto. }
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id, id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof.
  intros. destruct id1. destruct id2.
  assert (n <> n0). { unfold not. intros. rewrite H0 in H. auto. }
  remember (lt_eq_lt_dec n n0).
  inversion s.
  { inversion H1.
    { assert (n0 > n). { omega. } right. apply gt_conv. auto. }
    { omega. }
  }
  { assert (n > n0). { omega. } left. apply gt_conv. auto. }
Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id, id1 = id2 -> id1 >> id2 -> False.
Proof.
  intros. destruct id1. destruct id2.
  assert (n = n0). { inversion H. auto. }
  assert (n > n0). { inversion H0. auto. }
  rewrite H1 in H2.
  omega.
Qed.
