Require Export BigZ.
Require Export Id.
Require Export State.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

(* Type of binary operators *)
Inductive bop : Type :=
| Add : bop
| Sub : bop
| Mul : bop
| Div : bop
| Mod : bop
| Le  : bop
| Lt  : bop
| Ge  : bop
| Gt  : bop
| Eq  : bop
| Ne  : bop
| And : bop
| Or  : bop.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
| Nat : nat -> expr
| Var : id  -> expr              
| Bop : bop -> expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Bop Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Bop Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Bop Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity).

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.
  
Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.
   
Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Big-step evaluation relation *)
Inductive bs_eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : nat), [| Nat n |] s => (Z.of_nat n)
| bs_Var  : forall (s : state Z) (i : id) (z : Z), s / i => z -> [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [+] b |] s => (za + zb)
| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [-] b |] s => (za - zb)
| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [*] b |] s => (za * zb)
| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [/] b |] s => (Z.div za zb)
| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [<=] b |] s => Z.one
| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [<] b |] s => Z.one
| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [>=] b |] s => Z.one
| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [>] b |] s => Z.one
| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [>] b |] s => Z.zero

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [==] b |] s => Z.one
| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [/=] b |] s => Z.one
| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z), 
              [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (bs_eval e st z). 

Hint Constructors bs_eval.

Module SmokeTest.

  Lemma nat_always : 
    forall (n : nat) (s : state Z), [| Nat n |] s => (Z.of_nat n).
  Proof.
    intros.
    apply bs_Nat.
  Qed.

  Lemma double_and_sum : 
    forall (s : state Z) (e : expr) (z : Z), 
      [| e [*] (Nat 2) |] s => z -> [| e [+] e |] s => z.
  Proof.
    intros.
    inversion H.
    assert ((za * zb)%Z = (za + za)%Z).
    {
      assert (zb = (1+1)%Z).
      { inversion H5. simpl. reflexivity. }
      rewrite H6.
      omega.
    }
    rewrite H6.
    apply bs_Add.
    assumption.
    assumption.
  Qed.

End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Add : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [+]  b)
| v_Sub : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [-]  b)
| v_Mul : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [*]  b)
| v_Div : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/]  b)
| v_Mod : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [%]  b)
| v_Le  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<=] b)
| v_Lt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<]  b)
| v_Ge  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>=] b)
| v_Gt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>]  b)
| v_Eq  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [==] b)
| v_Ne  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/=] b)
| v_And : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [&]  b)
| v_Or  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [\/] b)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each its' variable is
   defined in that state
*)
Lemma defined_expression: forall (e : expr) (s : state Z) (z : Z) (id : id),
  [| e |] s => z -> id ? e -> exists z', s / id => z'.
Proof.
  intros e s.
  induction e.
  { intros. inversion H0. }
  {
    intros.
    exists z.
    inversion H0.
    rewrite H1 in H.
    inversion H.
    assumption.
  }
  (* TODO: How to make it non-repeatable? *)
  { intros z id H. inversion_clear H.
    intros Hid. inversion_clear Hid. destruct H as [H|H].
    apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
    apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
  { intros z id H. inversion_clear H.
    intros Hid. inversion_clear Hid. destruct H as [H|H].
    apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
    apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
  { intros z id H. inversion_clear H.
    intros Hid. inversion_clear Hid. destruct H as [H|H].
    apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
    apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
  { intros z id H. inversion_clear H.
    intros Hid. inversion_clear Hid. destruct H as [H|H].
    apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
    apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
  { intros z id H. inversion_clear H.
    intros Hid. inversion_clear Hid. destruct H as [H|H].
    apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
    apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
  { intros z id H. inversion_clear H.
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. } }
  { intros z id H. inversion_clear H.
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. } }
  { intros z id H. inversion_clear H.
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. } }
  { intros z id H. inversion_clear H.
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. } }
  { intros z id H. inversion_clear H.
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. } }
  { intros z id H. inversion_clear H.
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. } }
  { intros z id H. inversion_clear H.
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }}
  { intros z id H. inversion_clear H.
    {
      intros Hid. inversion_clear Hid. destruct H as [H|H].
      apply (IHe1 za id) in H0. destruct H0. exists x. auto. auto.
      apply (IHe2 zb id) in H1. destruct H1. exists x. auto. auto. }}
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable: forall (e : expr) (s : state Z) (id : id),
  id ? e -> (forall (z : Z), ~ (s / id => z)) -> (forall (z : Z), ~ ([| e |] s => z)).
Proof.
  induction e.
  { intros. exfalso. inversion H. }
  { intros. intro. inversion H. rewrite H2 in H1. inversion H1. remember (H0 z). contradiction. }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. } }
  { intros. intro. inversion_clear H. inversion_clear H2.
    {remember (IHe1 s id). inversion_clear H1. apply n with za in H. contradiction. assumption. }
    {remember (IHe2 s id). inversion_clear H1. apply n with zb in H. contradiction. assumption. } }
Qed.

(* The evaluation relation is deterministic *)
Lemma bs_eval_deterministic: forall (e : expr) (s : state Z) (z1 z2 : Z),
  [| e |] s => z1 -> [| e |] s => z2 -> z1 = z2.
Proof.
  induction e.
  { intros. inversion H. inversion H0. auto. }
  { intros. inversion_clear H. inversion_clear H0. apply state_deterministic with s i. assumption. assumption. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    rewrite H0. rewrite H4. reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    rewrite H0. rewrite H4. reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    rewrite H0. rewrite H4. reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    rewrite H0. rewrite H4. reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    rewrite H0. rewrite H4. reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    reflexivity.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    exfalso. rewrite H0 in H3. rewrite H6 in H3. contradiction.
    inversion H0.
    { exfalso. apply (IHe1 s za za0) in H5. apply (IHe2 s zb zb0) in H6. rewrite H5 in H3. rewrite H6 in H3. contradiction. assumption. assumption. }
    reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    reflexivity.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    exfalso. rewrite H0 in H3. rewrite H6 in H3. contradiction.
    inversion H0.
    { exfalso. apply (IHe1 s za za0) in H5. apply (IHe2 s zb zb0) in H6. rewrite H5 in H3. rewrite H6 in H3. contradiction. assumption. assumption. }
    reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    reflexivity.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    exfalso. rewrite H0 in H3. rewrite H6 in H3. contradiction.
    inversion H0.
    { exfalso. apply (IHe1 s za za0) in H5. apply (IHe2 s zb zb0) in H6. rewrite H5 in H3. rewrite H6 in H3. contradiction. assumption. assumption. }
    reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    reflexivity.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    exfalso. rewrite H0 in H3. rewrite H6 in H3. contradiction.
    inversion H0.
    { exfalso. apply (IHe1 s za za0) in H5. apply (IHe2 s zb zb0) in H6. rewrite H5 in H3. rewrite H6 in H3. contradiction. assumption. assumption. }
    reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    reflexivity.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    exfalso. rewrite H0 in H3. rewrite H6 in H3. contradiction.
    inversion H0.
    { exfalso. apply (IHe1 s za za0) in H5. apply (IHe2 s zb zb0) in H6. rewrite H5 in H3. rewrite H6 in H3. contradiction. assumption. assumption. }
    reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    reflexivity.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    exfalso. rewrite H0 in H3. rewrite H6 in H3. contradiction.
    inversion H0.
    { exfalso. apply (IHe1 s za za0) in H5. apply (IHe2 s zb zb0) in H6. rewrite H5 in H3. rewrite H6 in H3. contradiction. assumption. assumption. }
    reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    rewrite H0. rewrite H8. reflexivity. }
  { intros. inversion_clear H. inversion_clear H0.
    assert (za = za0). { apply (IHe1 s za za0). assumption. assumption. }
    assert (zb = zb0). { apply (IHe2 s zb zb0). assumption. assumption. }
    rewrite H0. rewrite H8. reflexivity. }
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 /id => z <-> s2 / id => z.

(* The result of expression evaluation in a state dependes only on the values
   of occurring variables
*)
Lemma variable_relevance: forall (e : expr) (s1 s2 : state Z) (z : Z),
  (forall (id : id) (z : Z), id ? e -> equivalent_states s1 s2 id) -> 
  [| e |] s1 => z -> [| e |] s2 => z.
Proof.
  induction e.
  { intros. inversion H0. apply (bs_Nat s2 n). }
  { intros. inversion H0. apply (bs_Var s2 i z). apply (H i).
    auto.
    apply v_Var.
    assumption. }
  { intros.
    inversion_clear H0. apply bs_Add.
    { apply (IHe1 s1 s2 za). intros.
      apply H. assumption. apply v_Add. left. assumption. assumption. }
    { apply (IHe2 s1 s2 zb). intros.
      apply H. assumption. apply v_Add. right. assumption. assumption. } }
  { intros.
    inversion_clear H0. apply bs_Sub.
    { apply (IHe1 s1 s2 za). intros.
      apply H. assumption. apply v_Sub. left. assumption. assumption. }
    { apply (IHe2 s1 s2 zb). intros.
      apply H. assumption. apply v_Sub. right. assumption. assumption. } }
  { intros.
    inversion_clear H0. apply bs_Mul.
    { apply (IHe1 s1 s2 za). intros.
      apply H. assumption. apply v_Mul. left. assumption. assumption. }
    { apply (IHe2 s1 s2 zb). intros.
      apply H. assumption. apply v_Mul. right. assumption. assumption. } }
  { intros.
    inversion_clear H0. apply bs_Div.
    { apply (IHe1 s1 s2 za). intros.
      apply H. assumption. apply v_Div. left. assumption. assumption. }
    { apply (IHe2 s1 s2 zb). intros.
      apply H. assumption. apply v_Div. right. assumption. assumption. } }
  { intros.
    inversion_clear H0. apply bs_Mod.
    { apply (IHe1 s1 s2 za). intros.
      apply H. assumption. apply v_Mod. left. assumption. assumption. }
    { apply (IHe2 s1 s2 zb). intros.
      apply H. assumption. apply v_Mod. right. assumption. assumption. } }
  { intros.
    inversion_clear H0.
    { apply (bs_Le_T s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Le. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Le. right. assumption. assumption. }
      assumption. }
    { apply (bs_Le_F s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Le. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Le. right. assumption. assumption. }
      assumption. } }
  { intros.
    inversion_clear H0.
    { apply (bs_Lt_T s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Lt. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Lt. right. assumption. assumption. }
      assumption. }
    { apply (bs_Lt_F s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Lt. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Lt. right. assumption. assumption. }
      assumption. } }
  { intros.
    inversion_clear H0.
    { apply (bs_Ge_T s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Ge. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Ge. right. assumption. assumption. }
      assumption. }
    { apply (bs_Ge_F s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Ge. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Ge. right. assumption. assumption. }
      assumption. } }
  { intros.
    inversion_clear H0.
    { apply (bs_Gt_T s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Gt. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Gt. right. assumption. assumption. }
      assumption. }
    { apply (bs_Gt_F s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Gt. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Gt. right. assumption. assumption. }
      assumption. } }
  { intros.
    inversion_clear H0.
    { apply (bs_Eq_T s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Eq. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Eq. right. assumption. assumption. }
      assumption. }
    { apply (bs_Eq_F s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Eq. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Eq. right. assumption. assumption. }
      assumption. } }
  { intros.
    inversion_clear H0.
    { apply (bs_Ne_T s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Ne. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Ne. right. assumption. assumption. }
      assumption. }
    { apply (bs_Ne_F s2 e1 e2 za zb).
      { apply (IHe1 s1 s2 za). intros. apply H. assumption. apply v_Ne. left. assumption. assumption. }
      { apply (IHe2 s1 s2 zb). intros. apply H. assumption. apply v_Ne. right. assumption. assumption. }
      assumption. } }
  { intros.
    inversion_clear H0. apply bs_And.
    { apply (IHe1 s1 s2 za). intros.
      apply H. assumption. apply v_And. left. assumption. assumption. }
    { apply (IHe2 s1 s2 zb). intros.
      apply H. assumption. apply v_And. right. assumption. assumption. }
      assumption. assumption. }
  { intros.
    inversion_clear H0. apply bs_Or.
    { apply (IHe1 s1 s2 za). intros.
      apply H. assumption. apply v_Or. left. assumption. assumption. }
    { apply (IHe2 s1 s2 zb). intros.
      apply H. assumption. apply v_Or. right. assumption. assumption. }
      assumption. assumption. }
Qed.


(* Semantic equivalence *)
Reserved Notation "e1 '~~' e2" (at level 42, no associativity).

Inductive equivalent: relation expr :=
  eq_intro : forall (e1 e2 : expr), 
               (forall (n : Z) (s : state Z), 
                 [| e1 |] s => n <-> [| e2 |] s => n
               ) -> e1 ~~ e2
where "e1 '~~' e2" := (equivalent e1 e2).

(* Semantic equivalence is an equivalence relation *)
Lemma eq_refl: forall (e : expr), e ~~ e.
Proof.
  intros.
  apply eq_intro.
  intros.
  reflexivity.
Qed.

Lemma eq_symm: forall (e1 e2 : expr), e1 ~~ e2 -> e2 ~~ e1.
Proof.
  intros.
  apply eq_intro.
  intros.
  symmetry.
  destruct H.
  apply (H n s).
Qed.

Lemma eq_trans: forall (e1 e2 e3 : expr), e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Proof.
  intros.
  apply eq_intro.
  intros.
  destruct H.
  destruct H0.
  rewrite (H n s).
  apply (H0 n s).
Qed.

Instance eq_equiv: Equivalence equivalent.
Proof.
  split.
  { split. remember (eq_refl x). inversion e. assumption. }
  { split. remember (eq_symm x y). apply e in H. destruct H. assumption. }
  { split. remember (eq_trans x y z). apply e in H. destruct H. assumption. assumption. }
Qed.

Example test_eq_refl : (Nat 1) ~~ (Nat 1).
Proof. reflexivity. Qed.
Example test_eq_symm : (forall a b: expr, (a ~~ b) -> (b ~~ a)).
Proof. intros. symmetry. assumption. Qed.

(* Contexts *)
Inductive Context : Type :=
| Hole : Context
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

(* Plugging an expression into a context *)
Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b (plug C e) e1
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: expr -> expr -> Prop :=
  ceq_intro : forall (e1 e2 : expr),
                (forall (C : Context), (C <~ e1) ~~ (C <~ e2)) -> e1 ~c~ e2
where "e1 '~c~' e2" := (contextual_equivalent e1 e2).

(* Context equivalence is an equivalence relation *)
Lemma ceq_refl: forall (e : expr), e ~c~ e.
Proof.
  intros.
  apply ceq_intro.
  intros.
  reflexivity.
Qed.

Lemma ceq_symm: forall (e1 e2 : expr), e1 ~c~ e2 -> e2 ~c~ e1.
Proof.
  intros.
  apply ceq_intro.
  intros.
  symmetry.
  destruct H.
  apply (H C).
Qed.

Lemma ceq_trans: forall (e1 e2 e3 : expr), e1 ~c~ e2 -> e2 ~c~ e3 -> e1 ~c~ e3.
Proof.
  intros.
  apply ceq_intro.
  intros.
  destruct H.
  destruct H0.
  rewrite (H C).
  apply (H0 C).
Qed.

Instance ceq_equiv: Equivalence contextual_equivalent.
Proof.
  split.
  { split. remember (ceq_refl x). inversion c. assumption. }
  { split. remember (ceq_symm x y). apply c in H. destruct H. assumption. }
  { split. remember (ceq_trans x y z). apply c in H. destruct H. assumption. assumption. }
Qed.

Lemma ceq_hole_eq: forall e : expr, (Hole <~ e) = e.
Proof. auto. Qed.

Lemma eq_eq_ceq_one_side:
  forall e1 e2 : expr, forall C: Context, forall n: Z, forall s: state Z,
  (e1 ~~ e2) -> [|C <~ e1|] s => (n) -> [|C <~ e2|] s => (n).
Proof.
  intros e1 e2 C.
  induction C.
  { intros. destruct H. apply (H n s). rewrite <-(ceq_hole_eq e1). assumption. }

  { intros. assert (forall e1, (AddL C e <~ e1) = (Add (C <~ e1) e)). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Add. apply IHC. assumption. assumption. assumption. }
  { intros. assert (forall e1, (SubL C e <~ e1) = (Sub (C <~ e1) e)). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Sub. apply IHC. assumption. assumption. assumption. }
  { intros. assert (forall e1, (MulL C e <~ e1) = (Mul (C <~ e1) e)). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Mul. apply IHC. assumption. assumption. assumption. }
  { intros. assert (forall e1, (DivL C e <~ e1) = (Div (C <~ e1) e)). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Div. apply IHC. assumption. assumption. assumption. }
  { intros. assert (forall e1, (ModL C e <~ e1) = (Mod (C <~ e1) e)). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Mod. apply IHC. assumption. assumption. assumption. }
  { intros. assert (forall e1, (LeL C e <~ e1) = (Le (C <~ e1) e)). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Le_T s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption.
    apply (bs_Le_F s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption. }
  { intros. assert (forall e1, (LtL C e <~ e1) = (Lt (C <~ e1) e)). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Lt_T s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption.
    apply (bs_Lt_F s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption. }
  { intros. assert (forall e1, (GeL C e <~ e1) = (Ge (C <~ e1) e)). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Ge_T s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption.
    apply (bs_Ge_F s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption. }
  { intros. assert (forall e1, (GtL C e <~ e1) = (Gt (C <~ e1) e)). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Gt_T s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption.
    apply (bs_Gt_F s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption. }
  { intros. assert (forall e1, (EqL C e <~ e1) = (Eq (C <~ e1) e)). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Eq_T s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption.
    apply (bs_Eq_F s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption. }
  { intros. assert (forall e1, (NeL C e <~ e1) = (Ne (C <~ e1) e)). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Ne_T s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption.
    apply (bs_Ne_F s (C <~ e2) e za zb). apply (IHC za s). assumption. assumption. assumption. assumption. }
  { intros. assert (forall e1, (AndL C e <~ e1) = (And (C <~ e1) e)). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_And. apply IHC. assumption. assumption. assumption. assumption. assumption. }
  { intros. assert (forall e1, (OrL C e <~ e1) = (Or (C <~ e1) e)). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Or. apply IHC. assumption. assumption. assumption. assumption. assumption. }

  { intros. assert (forall e1, (AddR e C <~ e1) = (Add e (C <~ e1))). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Add. assumption. apply IHC. assumption. assumption. }
  { intros. assert (forall e1, (SubR e C <~ e1) = (Sub e (C <~ e1))). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Sub. assumption. apply IHC. assumption. assumption. }
  { intros. assert (forall e1, (MulR e C <~ e1) = (Mul e (C <~ e1))). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Mul. assumption. apply IHC. assumption. assumption. }
  { intros. assert (forall e1, (DivR e C <~ e1) = (Div e (C <~ e1))). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Div. assumption. apply IHC. assumption. assumption. }
  { intros. assert (forall e1, (ModR e C <~ e1) = (Mod e (C <~ e1))). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Mod. assumption. apply IHC. assumption. assumption. }
  { intros. assert (forall e1, (LeR e C <~ e1) = (Le e (C <~ e1))). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Le_T s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption.
    apply (bs_Le_F s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption. }
  { intros. assert (forall e1, (LtR e C <~ e1) = (Lt e (C <~ e1))). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Lt_T s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption.
    apply (bs_Lt_F s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption. }
  { intros. assert (forall e1, (GeR e C <~ e1) = (Ge e (C <~ e1))). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Ge_T s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption.
    apply (bs_Ge_F s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption. }
  { intros. assert (forall e1, (GtR e C <~ e1) = (Gt e (C <~ e1))). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Gt_T s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption.
    apply (bs_Gt_F s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption. }
  { intros. assert (forall e1, (EqR e C <~ e1) = (Eq e (C <~ e1))). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Eq_T s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption.
    apply (bs_Eq_F s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption. }
  { intros. assert (forall e1, (NeR e C <~ e1) = (Ne e (C <~ e1))). auto.
    rewrite H1 in H0. rewrite H1. inversion_clear H0.
    apply (bs_Ne_T s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption.
    apply (bs_Ne_F s e (C <~ e2) za zb). assumption. apply (IHC zb s). assumption. assumption. assumption. }
  { intros. assert (forall e1, (AndR e C <~ e1) = (And e (C <~ e1))). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_And. assumption. apply IHC. assumption. assumption. assumption. assumption. }
  { intros. assert (forall e1, (OrR e C <~ e1) = (Or e (C <~ e1))). auto.
    rewrite H1 in H0. inversion_clear H0.
    rewrite H1. apply bs_Or. assumption. apply IHC. assumption. assumption. assumption. assumption. }
Qed.

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (e1 e2 : expr), e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  intros.
  split.
  {
    intros. apply ceq_intro. intros. apply eq_intro. intros.
    split.
    apply (eq_eq_ceq_one_side e1 e2). assumption.
    apply (eq_eq_ceq_one_side e2 e1). symmetry. assumption.
  }
  { intros. apply eq_intro. intros.
    destruct H.
    remember (H Hole).
    inversion_clear e.
    remember (H0 n s).
    rewrite <-(ceq_hole_eq e1).
    rewrite <-(ceq_hole_eq e2).
    assumption.
  }
Qed.

















 


  