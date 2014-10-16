Require Import ssreflect ssrfun ssrbool.

Lemma t1 P : False -> P.
Proof. done. Qed.

Lemma t3 (P : Prop) : P -> ~ ~ P.
Proof. move => H nP; apply: (nP H). Qed.

Lemma t5 (P : Prop) : ~ ~ ~ P -> ~ P.
Proof.
move=> H HP; apply: H.
by apply: t3.
Qed.

(* False

Lemma t6 (P Q : Prop) : (~ Q -> ~ P) -> (P -> Q).
Proof. Qed.
*)

Lemma t7 (P Q : Prop) : (P -> Q) -> (~ Q -> ~ P).
Proof. move => PQ nQ HP; apply: (nQ (PQ HP)). Qed.

(* False
Lemma t8 (P Q : Prop) : ~ (P /\ Q) -> (~ P \/ ~ Q).
Proof.
move=> nPQ.
*)

Lemma t9 (P Q : Prop) : (~ P \/ ~ Q) -> ~ (P /\ Q).
Proof.
case => H; case; last by move => _.
by move/H.
Qed.

(* False
Lemma t10 (P Q R : Prop) : ((P <-> Q) <-> R) <-> (P <-> (Q <-> R)).
Proof.
split; case => H1 H2; split => H3.
- split => H4; first by apply H1; split.
  move: (H2 H4); case.
  by move=> H5 _; apply: H5.
- move: H3; case.
*)

Lemma t11 (P Q R : Prop) : ((P /\ Q) -> R) <-> (P -> (Q -> R)).
Proof.
split.
- move=> H HP HQ; apply: H.
  by split.
by move=> H; case.
Qed.

(* False
Lemma t12 (P Q : Prop) : (P -> Q) <-> (~ P \/ Q).
Proof.
split; last case => //.

Qed.
*)

Lemma ex1 (P Q : Prop) : ~ (P \/ Q) -> (~ P /\ ~ Q).
Proof.
by move=> H; split; move=> H'; apply H; [left | right].
Qed.

Lemma t13 (P : Prop) : ~ ~ (P \/ ~ P).
Proof. by move/ex1; case. Qed.