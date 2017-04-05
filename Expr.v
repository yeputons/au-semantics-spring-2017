Require Export BigZ.
Require Export Id.
Require Export State.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
  | Nat : nat  -> expr
  | Var : id   -> expr              
  | Add : expr -> expr -> expr
  | Sub : expr -> expr -> expr
  | Mul : expr -> expr -> expr
  | Div : expr -> expr -> expr
  | Mod : expr -> expr -> expr
  | Le  : expr -> expr -> expr
  | Lt  : expr -> expr -> expr
  | Ge  : expr -> expr -> expr
  | Gt  : expr -> expr -> expr
  | Eq  : expr -> expr -> expr
  | Ne  : expr -> expr -> expr
  | And : expr -> expr -> expr
  | Or  : expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Or  x y) (at level 38, left associativity).

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

Inductive equivalent: expr -> expr -> Prop := 
  eq_intro : forall (e1 e2 : expr), 
               (forall (n : Z) (s : state Z), 
                 [| e1 |] s => n <-> [| e2 |] s => n
               ) -> e1 ~~ e2
where "e1 '~~' e2" := (equivalent e1 e2).

(* Semantic equivalence is an equivalence relation *)
Lemma eq_refl: forall (e : expr), e ~~ e.
Proof. admit. Admitted.

Lemma eq_symm: forall (e1 e2 : expr), e1 ~~ e2 -> e2 ~~ e1.
Proof. admit. Admitted.

Lemma eq_trans: forall (e1 e2 e3 : expr), e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Proof. admit. Admitted.
 
(* Contexts *)
Inductive Context : Type :=
  | Hole : Context
  | AddL : Context -> expr -> Context
  | SubL : Context -> expr -> Context
  | MulL : Context -> expr -> Context
  | DivL : Context -> expr -> Context
  | ModL : Context -> expr -> Context
  | LeL  : Context -> expr -> Context
  | LtL  : Context -> expr -> Context
  | GeL  : Context -> expr -> Context
  | GtL  : Context -> expr -> Context
  | EqL  : Context -> expr -> Context
  | NeL  : Context -> expr -> Context
  | AndL : Context -> expr -> Context
  | OrL  : Context -> expr -> Context
  | AddR : expr -> Context -> Context
  | SubR : expr -> Context -> Context
  | MulR : expr -> Context -> Context
  | DivR : expr -> Context -> Context
  | ModR : expr -> Context -> Context
  | LeR  : expr -> Context -> Context
  | LtR  : expr -> Context -> Context
  | GeR  : expr -> Context -> Context
  | GtR  : expr -> Context -> Context
  | EqR  : expr -> Context -> Context
  | NeR  : expr -> Context -> Context
  | AndR : expr -> Context -> Context
  | OrR  : expr -> Context -> Context.

(* Plugging an expression into a context *)
Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | AddL C e1 => Add (plug C e) e1
  | SubL C e1 => Sub (plug C e) e1
  | MulL C e1 => Mul (plug C e) e1
  | DivL C e1 => Div (plug C e) e1
  | ModL C e1 => Mod (plug C e) e1
  | LeL  C e1 => Le  (plug C e) e1
  | LtL  C e1 => Lt  (plug C e) e1
  | GeL  C e1 => Ge  (plug C e) e1
  | GtL  C e1 => Gt  (plug C e) e1
  | EqL  C e1 => Eq  (plug C e) e1
  | NeL  C e1 => Ne  (plug C e) e1
  | AndL C e1 => And (plug C e) e1
  | OrL  C e1 => Or  (plug C e) e1
  | AddR e1 C => Add e1 (plug C e)
  | SubR e1 C => Sub e1 (plug C e)
  | MulR e1 C => Mul e1 (plug C e)
  | DivR e1 C => Div e1 (plug C e)
  | ModR e1 C => Mod e1 (plug C e)
  | LeR  e1 C => Le  e1 (plug C e)
  | LtR  e1 C => Lt  e1 (plug C e)
  | GeR  e1 C => Ge  e1 (plug C e)
  | GtR  e1 C => Gt  e1 (plug C e)
  | EqR  e1 C => Eq  e1 (plug C e)
  | NeR  e1 C => Ne  e1 (plug C e)
  | AndR e1 C => And e1 (plug C e)
  | OrR  e1 C => Or  e1 (plug C e)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: expr -> expr -> Prop :=
  ceq_intro : forall (e1 e2 : expr),
                (forall (C : Context), (C <~ e1) ~~ (C <~ e2)) -> e1 ~c~ e2
where "e1 '~c~' e2" := (contextual_equivalent e1 e2).

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (e1 e2 : expr), e1 ~~ e2 <-> e1 ~c~ e2.
Proof. admit. Admitted.




















 


  