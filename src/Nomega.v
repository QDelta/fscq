(* Make [lia] work for [N] *)

Require Import Arith Lia NArith.

Local Open Scope N_scope.

Hint Rewrite Nplus_0_r nat_of_Nsucc nat_of_Nplus nat_of_Nminus
  N_of_nat_of_N nat_of_N_of_nat
  Pnat.nat_of_P_o_P_of_succ_nat_eq_succ Pnat.nat_of_P_succ_morphism : N.

Theorem nat_of_N_eq : forall n m,
  nat_of_N n = nat_of_N m
  -> n = m.
Proof.
  intros ? ? H; apply (f_equal N_of_nat) in H;
    autorewrite with N in *; assumption.
Qed.

Theorem Nneq_in : forall n m,
  nat_of_N n <> nat_of_N m
  -> n <> m.
Proof.
  congruence.
Qed.

Theorem Nneq_out : forall n m,
  n <> m
  -> nat_of_N n <> nat_of_N m.
Proof.
  lia.
Qed.

Theorem Nlt_out : forall n m, n < m
  -> (nat_of_N n < nat_of_N m)%nat.
Proof.
  unfold N.lt; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_Lt_lt; assumption.
Qed.

Theorem Nlt_in : forall n m, (nat_of_N n < nat_of_N m)%nat
  -> n < m.
Proof.
  unfold N.lt; intros.
  rewrite nat_of_Ncompare.
  apply (proj1 (nat_compare_lt _ _)); assumption.
Qed.

Theorem Nge_out : forall n m, n >= m
  -> (nat_of_N n >= nat_of_N m)%nat.
Proof.
  unfold N.ge; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_ge; assumption.
Qed.

Theorem Nge_in : forall n m, (nat_of_N n >= nat_of_N m)%nat
  -> n >= m.
Proof.
  unfold N.ge; intros.
  rewrite nat_of_Ncompare.
  apply nat_compare_ge; assumption.
Qed.

Ltac nsimp H := simpl in H; repeat progress (autorewrite with N in H; simpl in H).
