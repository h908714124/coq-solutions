Require Import List.
Import ListNotations.

Inductive nostutter: list nat -> Prop :=
 | case_0 : nostutter []
 | case_1 : forall (n : nat), nostutter [n]
 | case_2 : forall (n : nat) (v : list nat)
              (H : nostutter v)
              (P : n <> hd 0 v),
     nostutter (n :: v).

Example test_nostutter_1: nostutter [3; 1; 4; 1; 5; 6].
Proof.
  repeat constructor.
  auto; simpl.
  auto; simpl.
  auto; simpl.
  auto; simpl.
  auto; simpl.
  auto; simpl.
  auto; simpl.
  auto; simpl.
  auto; simpl.
  auto; simpl.
Qed.

Example test_nostutter_2: nostutter nil.
Proof.
  apply case_0.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  apply case_1.
Qed.

Example test_nostutter_4: not (nostutter [3; 1; 1; 4]).  
Proof.
  intro H.
  repeat match goal with h: nostutter _ |- _ => inversion h; clear h; subst end.
  contradiction P0.
  auto.
  contradiction P0.
  auto.
Qed.
