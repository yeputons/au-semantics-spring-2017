Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Require Export BigZ.
Require Export Id.
Require Export State.
Require Export Expr.

(* The type of statements *)
Inductive stmt : Type :=
  | SKIP  : stmt
  | Assn  : id -> expr -> stmt
  | READ  : id -> stmt
  | WRITE : expr -> stmt
  | Seq   : stmt -> stmt -> stmt
  | If    : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

Reserved Notation "c1 '==' s '==>' c2" (at level 0).

(* Big-step evaluation relation *)
Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
  | bs_Skip        : forall (c : conf), c == SKIP ==> c 
  | bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) == x ::= e ==> (s [x <- z], i, o)
  | bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                       (s, z::i, o) == READ x ==> (s [x <- z], i, o)
  | bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) == WRITE e ==> (s, i, z::o)
  | bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt),
                       c == s1 ==> c' -> c' == s2 ==> c'' -> c ==  s1 ;; s2 ==> c''
  | bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                       [| e |] s => Z.one -> (s, i, o) == s1 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
  | bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                       [| e |] s => Z.zero -> (s, i, o) == s2 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
  | bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt),
                       [| e |] st => Z.one -> (st, i, o) == s ==> c' -> c' == WHILE e DO s END ==> c'' ->
                          (st, i, o) == WHILE e DO s END ==> c''
  | bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt),
                       [| e |] st => Z.zero -> (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

Lemma bs_eval_deterministic_one_zero: forall (e : expr) (s : state Z),
  [| e |] s => Z.zero -> [| e |] s => Z.one -> False.
Proof.
  intros.
  assert (Z.zero = Z.one).
  apply (bs_eval_deterministic e s Z.zero Z.one). assumption. assumption.
  inversion H1.
Qed.

(* Big-step semantics is deterministic *)
Lemma bs_int_deterministic : forall (c c1 c2 : conf) (s : stmt), c == s ==> c1 -> c == s ==> c2 -> c1 = c2.
Proof.
  cut (forall (s : stmt) (c c1 : conf), c == s ==> c1 -> forall (c2 : conf), c == s ==> c2 -> c1 = c2).
  { firstorder. }
  intros s c c1 H.
  induction H.
  - intros. inversion H. reflexivity.
  - intros. inversion H0. apply (bs_eval_deterministic e s z z0) in H. rewrite H. reflexivity. assumption.
  - intros. inversion H. reflexivity.
  - intros. inversion H0. apply (bs_eval_deterministic e s z z0) in H. rewrite H. reflexivity. assumption.
  - intros. inversion H1.
    assert (c' = c'0).
    { apply (IHbs_int1 c'0). assumption. }
    rewrite <-H8 in H7. apply (IHbs_int2 c2). assumption.
  - intros. inversion H1.
    + apply (IHbs_int c2) in H10. assumption.
    + apply (bs_eval_deterministic_one_zero e s) in H. exfalso. assumption. assumption.
  - intros. inversion H1.
    + apply (bs_eval_deterministic_one_zero e s) in H. exfalso. assumption. assumption.
    + apply (IHbs_int c2) in H10. assumption.
  - intros. inversion H2.
    + assert (c' = c'0). auto. rewrite <-H12 in H11. apply IHbs_int2. assumption.
    + apply (bs_eval_deterministic_one_zero e st) in H. exfalso. assumption. assumption.
  - intros. inversion H0.
    + apply (bs_eval_deterministic_one_zero e st) in H. exfalso. assumption. assumption.
    + reflexivity.
Qed.

Reserved Notation "s1 '~~~' s2" (at level 0).

Inductive bs_equivalent: stmt -> stmt -> Prop :=
  bs_eq_intro: forall (s1 s2 : stmt), 
                 (forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c') -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

Instance : Equivalence bs_equivalent.
Proof.
  split; constructor; intros c c'; constructor; intros Hc;
    try assumption;
    try (inversion_clear H; apply H0; assumption).
    - inversion_clear H as [a b H']. inversion H0 as [a b H'']. apply H''. apply H'. assumption.
    - inversion_clear H as [a b H']. inversion H0 as [a b H'']. apply H'. apply H''. assumption.
Qed.

Ltac rewrite_bs_equivalent H :=
  match type of H with
  | ?s1 ~~~ ?s2 =>
    match goal with
    | |- ?c1 == ?s2 ==> ?c2 =>
      let a := fresh in
      let b := fresh in
      let H' := fresh in
      let c := fresh in
      let d := fresh in
      inversion H as [a b H' c d]; apply H'; clear d c H' a b
    | |- ?c1 == ?s1 ==> ?c2 =>
      let a := fresh in
      let b := fresh in
      let H' := fresh in
      let c := fresh in
      let d := fresh in
      inversion H as [a b H' c d]; apply H'; clear d c H' a b
    end
  end.

Ltac inversion_seq_all :=
  match goal with
  | H: _ == _;; _ ==> _ |- _ => inversion_clear H; try inversion_seq_all
  end.

Ltac apply_seq_all :=
  match goal with
  | H: ?c1 == ?s1 ==> ?c2 |- ?c1 == ?s1;; _ ==> _ =>
    apply bs_Seq with c2; solve [assumption|solve [apply_seq_all|assumption]]
  | H: ?c2 == ?s2 ==> ?c3 |- ?c1 == _;; ?s2 ==> ?c3 =>
    apply bs_Seq with c2; solve [assumption|solve [apply_seq_all|assumption]]
  end.

Module SmokeTest.
  Lemma bs_equivalent_1 : forall (s1 s2 : stmt) (c1 c2 : conf),
      (s1 ~~~ s2) -> (c1 == s1 ==> c2) -> (c1 == s2 ==> c2).
  Proof.
    intros. rewrite_bs_equivalent H. assumption.
  Qed.
  Lemma bs_equivalent_2 : forall (s1 s2 : stmt) (c1 c2 : conf),
      (s2 ~~~ s1) -> (c1 == s1 ==> c2) -> (c1 == s2 ==> c2).
  Proof.
    intros. rewrite_bs_equivalent H. assumption.
  Qed.

  Lemma seq_assoc : forall (s1 s2 s3 : stmt),
                      ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    intros s1 s2 s3. constructor. intros c c'.
    split; intros H; inversion_seq_all; apply_seq_all.
  Qed.

  Lemma while_unfolds : forall (e : expr) (s : stmt),
                          (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    intros e s. constructor. intros [[st i] o] [[st' i'] o'].
    split.
    - intros H. inversion H.
      + constructor. assumption. apply_seq_all.
      + apply bs_If_False. assumption. apply bs_Skip.
    - intros H. inversion H.
      + inversion_seq_all. apply bs_While_True with c'0; assumption.
      + inversion H8. apply bs_While_False. congruence.
  Qed.

  Lemma while_false : forall (e : expr) (s : stmt) (st : state Z) (i o : list Z) (c : conf),
                        c == WHILE e DO s END ==> (st, i, o) -> [| e |] st => Z.zero.
  Proof.
    intros e s st i o c H.
    remember (st, i, o).
    remember (WHILE e DO s END).
    induction H.
    - inversion Heqs0.
    - inversion Heqs0.
    - inversion Heqs0.
    - inversion Heqs0.
    - inversion Heqs0.
    - inversion Heqs0.
    - inversion Heqs0.
    - apply IHbs_int2. assumption. assumption.
    - inversion Heqs0 as [[He Hs]]. rewrite <-He.
      inversion Heqp as [[Hst Hi Ho]]. rewrite <-Hst.
      assumption.
  Qed.

  Definition True := Nat 1.

  Lemma loop_eq_undefined : (WHILE True DO SKIP END) ~~~ (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    constructor. intros [[st i] o] [[st' i'] o']. split.
    - intros H. remember (WHILE True DO SKIP END). induction H; inversion Heqs.
      + apply IHbs_int2 in Heqs. rewrite H4 in H0. inversion H0. rewrite H6. assumption.
      + rewrite H1 in H. inversion H.
    - intros H. inversion H.
      + inversion H7.
      + inversion H7.
  Qed.
  
End SmokeTest.

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: stmt -> stmt -> Prop :=
  ceq_intro : forall (s1 s2 : stmt),
                (forall (C : Context), (C <~ s1) ~~~ (C <~ s2)) -> s1 ~c~ s2
where "s1 '~c~' s2" := (contextual_equivalent s1 s2).

Instance : Equivalence contextual_equivalent.
Proof.
  constructor; constructor; intros C.
  - constructor. split; intros; assumption.
  - symmetry. inversion H as [a b H']. apply H'.
  - transitivity (C <~ y).
    + inversion H as [a b H']. apply H'.
    + inversion H0 as [a b H0']. apply H0'.
Qed.

Ltac apply_in_some x :=
  match goal with
  | H : _ |- _ => apply x in H
  end.

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (s1 s2 : stmt), s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
  intros s1 s2; split; intros H.
  { (* ~~~ -> ~c~ *)
    constructor. intros C. induction C; simpl; try assumption; constructor; intros c c'.
    - split; intros H'; inversion_seq_all; inversion IHC as [a b IHC']; apply_in_some IHC'; apply_seq_all.
    - split; intros H'; inversion_seq_all; inversion IHC as [a b IHC']; apply_in_some IHC'; apply_seq_all.
    - split; (intros H'; inversion H';
          (apply bs_If_True + apply bs_If_False); solve [assumption|rewrite_bs_equivalent IHC; assumption]).
    - split; (intros H'; inversion H';
          (apply bs_If_True + apply bs_If_False); solve [assumption|rewrite_bs_equivalent IHC; assumption]).
    - split; (
        intros H';
        [remember (WHILE e DO C <~ s1 END) as L + remember (WHILE e DO C <~ s2 END) as L];
        induction H'; inversion HeqL;
        [ apply bs_While_True with c';
          [ rewrite <-H2; assumption
          | rewrite_bs_equivalent IHC; congruence
          | apply IHH'2; congruence ]
        | apply bs_While_False; congruence ]
      ).
  }
  { (* ~c~ -> ~~~ *)
    inversion H.
    cut ((Hole <~ s1) ~~~ (Hole <~ s2)).
    + simpl. intros. assumption.
    + apply H0.
  }
Qed.

(* CPS-style semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.
 
Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont), 
                      KEmpty |- c -- k --> c' -> 
                      k |- c -- !SKIP --> c'
| cps_Assn        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (e : expr) (n : Z),
                      [| e |] s => n ->
                      KEmpty |- (s [x <- n], i, o) -- k --> c' ->
                      k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (z : Z),
                      KEmpty |- (s [x <- z], i, o) -- k --> c' ->
                      k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (z : Z),
                      [| e |] s => z ->
                      KEmpty |- (s, i, z::o) -- k --> c' ->
                      k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt), 
                      !s2 @ k |- c -- !s1 --> c' ->
                      k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.one ->
                      k |- (s, i, o) -- !s1 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.zero ->
                      k |- (s, i, o) -- !s2 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
                      [| e |] st => Z.one ->
                      !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c' ->
                      k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
                      [| e |] st => Z.zero ->
                      KEmpty |- (st, i, o) -- k --> c' ->
                      k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Lemma bs_int_to_cps_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  (st, i, o) == s ==> c' -> KEmpty |- (st, i, o) -- !s --> c'.
Proof. admit. Admitted.

Lemma cps_int_to_bs_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  KEmpty |- (st, i, o) -- !s --> c' -> (st, i, o) == s ==> c'.
Proof. admit. Admitted.
