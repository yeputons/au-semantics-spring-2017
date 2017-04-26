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
| v_Bop : forall (id : id) (op : bop) (a b : expr), id ? a \/ id ? b -> id ? (Bop op a b)
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
  { intros z id H Hid. inversion Hid. inversion H4.
    - inversion H; apply (IHe1 za id); assumption.
    - inversion H; apply (IHe2 zb id); assumption. }
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
  { intros s id H Huf z Hw.
    inversion_clear H. inversion H0.
    - inversion Hw; apply (IHe1 s id H Huf za); assumption.
    - inversion Hw; apply (IHe2 s id H Huf zb); assumption. }
Qed.

(* The evaluation relation is deterministic *)
Lemma bs_eval_deterministic: forall (e : expr) (s : state Z) (z1 z2 : Z),
  [| e |] s => z1 -> [| e |] s => z2 -> z1 = z2.
Proof.
  induction e.
  { intros. inversion H. inversion H0. auto. }
  { intros. inversion_clear H. inversion_clear H0. apply state_deterministic with s i. assumption. assumption. }
  { intros s z1 z2 H1 H2.
    destruct b;
    inversion_clear H1; inversion_clear H2; try solve
    [ reflexivity
    | match goal with
      | Ha: [|e1|] s => ?za, Ha0: [|e1|] s => ?za0
      , Hb: [|e2|] s => ?zb, Hb0: [|e2|] s => ?zb0
      |- _ =>
        rewrite (IHe1 s za za0 Ha Ha0);
        rewrite (IHe2 s zb zb0 Hb Hb0);
        reflexivity

      | Ha: [|e1|] s => ?za, Ha0: [|e1|] s => ?za0
      , Hb: [|e2|] s => ?zb, Hb0: [|e2|] s => ?zb0
      , H1: _%Z, H2: _%Z
      |- _ =>
        exfalso;
        rewrite (IHe1 s za za0 Ha Ha0) in H1;
        rewrite (IHe2 s zb zb0 Hb Hb0) in H2;
        solve [contradiction | omega]
      end
    ]. }
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
  {
    intros s1 s2 z Hv H.
    inversion_clear H;
    assert (He1: [|e1|] s2 => za);
    assert (He2: [|e2|] s2 => zb);
    try (
      apply IHe1 with s1 + apply IHe2 with s1; solve
      [ intros id v H';
        apply Hv; solve
        [ apply v
        | constructor; left + right; assumption
        | assumption ]
      | assumption ] );
    try (constructor; assumption).
    - apply bs_Le_T with za zb; assumption.
    - apply bs_Le_F with za zb; assumption.
    - apply bs_Lt_T with za zb; assumption.
    - apply bs_Lt_F with za zb; assumption.
    - apply bs_Ge_T with za zb; assumption.
    - apply bs_Ge_F with za zb; assumption.
    - apply bs_Gt_T with za zb; assumption.
    - apply bs_Gt_F with za zb; assumption.
    - apply bs_Eq_T with za zb; assumption.
    - apply bs_Eq_F with za zb; assumption.
    - apply bs_Ne_T with za zb; assumption.
    - apply bs_Ne_F with za zb; assumption.
  }
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
  | BopR b e1 C => Bop b e1 (plug C e)
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
  { intros n s He H.
    assert (H': forall e', BopL b C e <~ e' = Bop b (C <~ e') e). reflexivity.
    rewrite H' in H.
    rewrite H'.

    inversion H; try (
       constructor
    || apply bs_Le_T with za zb
    || apply bs_Le_F with za zb
    || apply bs_Lt_T with za zb
    || apply bs_Lt_F with za zb
    || apply bs_Ge_T with za zb
    || apply bs_Ge_F with za zb
    || apply bs_Gt_T with za zb
    || apply bs_Gt_F with za zb
    || apply bs_Eq_T with za zb
    || apply bs_Eq_F with za zb
    || apply bs_Ne_T with za zb
    || apply bs_Ne_F with za zb
    ;
    solve [ apply IHC; assumption | assumption ]
    ). }
  { intros n s He H.
    assert (H': forall e', BopR b e C <~ e' = Bop b e (C <~ e')). reflexivity.
    rewrite H' in H.
    rewrite H'.
    inversion H; try (
       constructor
    || apply bs_Le_T with za zb
    || apply bs_Le_F with za zb
    || apply bs_Lt_T with za zb
    || apply bs_Lt_F with za zb
    || apply bs_Ge_T with za zb
    || apply bs_Ge_F with za zb
    || apply bs_Gt_T with za zb
    || apply bs_Gt_F with za zb
    || apply bs_Eq_T with za zb
    || apply bs_Eq_F with za zb
    || apply bs_Ne_T with za zb
    || apply bs_Ne_F with za zb
    ;
    solve [ apply IHC; assumption | assumption ]
    ). }
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

















 


  