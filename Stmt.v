Require Import List.
Import ListNotations.
Require Import Omega.

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

(* Big-step semantics is deterministic *)
Lemma bs_int_deterministic : forall (c c1 c2 : conf) (s : stmt), c == s ==> c1 -> c == s ==> c2 -> c1 = c2.
Proof. admit. Admitted.

Reserved Notation "s1 '~~~' s2" (at level 0).

Inductive bs_equivalent: stmt -> stmt -> Prop :=
  bs_eq_intro: forall (s1 s2 : stmt), 
                 (forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c') -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

Module SmokeTest.

  Lemma seq_assoc : forall (s1 s2 s3 : stmt) (c c' : conf),
                      ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof. admit. Admitted.

  Lemma while_unfolds : forall (e : expr) (s : stmt) (c c' : conf),
                          (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. admit. Admitted.    

  Lemma while_false : forall (e : expr) (s : stmt) (st : state Z) (i o : list Z) (c : conf),
                        c == WHILE e DO s END ==> (st, i, o) -> [| e |] st => Z.zero.
  Proof. admit. Admitted.

  Definition True := Nat 1.

  Lemma loop_eq_undefined : (WHILE True DO SKIP END) ~~~ (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. admit. Admitted.
  
End SmokeTest.

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
