Require Import Arith.
Require Import Lia.
Require Import List.
Require Import Recdef.

(* We define 'ht' following the blog post. *)
Definition ht (n : nat) : nat :=
  2 + 3 * (n / 2).

(* Now we use a 2-adic valuation that we will use as measure for our recursion. *)

Function two_adic_valuation (n : nat) {measure id n} :=
  match n, (n mod 2) with
    | 0, _ => 0
    | _, 0 => S (two_adic_valuation (n / 2))
    | _, _ => 0
  end.
Proof.
  intros _ n _ Sn_is_even; unfold id.
  apply Nat.div_lt; lia.
Defined.

Definition two_adic_valuation_S (n : nat) :=
  two_adic_valuation (S n).

(* Proving some basic properties of the 2-adic valuation. *)

Lemma two_adic_valuation_mult_3:
  forall (n : nat),
  two_adic_valuation (3 * n) = two_adic_valuation n.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  destruct_with_eqn n; try now compute.
  rewrite two_adic_valuation_equation with (n := S n0).
  rewrite two_adic_valuation_equation with (n := 3 * S n0).
  remember (3 * S n0 - 1) as n2.
  replace (3 * S n0) with (S n2) by lia.
  replace (S n2) with (3 * n) in * by lia; clear n2 Heqn2.
  assert (n > 0) by lia; replace (S n0) with n in * by lia; clear n0 Heqn0.
  rewrite Nat.mul_mod by lia; replace (3 mod 2) with 1 by now compute.
  rewrite Nat.mul_1_l, Nat.mod_mod by lia.
  destruct_with_eqn (n mod 2); try lia.
  apply f_equal; rewrite Nat.divide_div_mul_exact; try lia.
  + rewrite IHn; auto.
    apply Nat.div_lt; lia.
  + apply Nat.mod_divide; lia.
Qed.

Lemma two_adic_valuation_div_2:
  forall (n : nat),
  0 < n ->
  n mod 2 = 0 ->
  S (two_adic_valuation (n / 2)) = two_adic_valuation n.
Proof.
  intros n n_gt_0 n_is_even.
  rewrite two_adic_valuation_equation with (n := n).
  destruct_with_eqn n; try now compute.
  rewrite n_is_even; lia.
Qed.

Theorem ht_decreases_odd_two_adic_valuation_S_by_one:
  forall (n : nat),
  n mod 2 <> 0 ->
  two_adic_valuation_S (ht n) + 1 = two_adic_valuation_S n.
Proof.
  intros n n_is_odd; unfold two_adic_valuation_S, ht.
  replace (S (2 + 3 * (n / 2))) with (3 * (S (n / 2))) by lia.
  rewrite two_adic_valuation_mult_3 by lia.
  assert (n mod 2 < 2) by now apply Nat.mod_upper_bound.
  assert (S n mod 2 = 0).
  {
    replace (S n) with (n + 1) by lia; rewrite Nat.add_mod by lia.
    replace (n mod 2) with 1 by lia; now compute.
  }
  rewrite <-two_adic_valuation_div_2 with (n := S n); try lia.
  replace (S (n / 2)) with (S n / 2); try lia.
  rewrite <-Nat.mul_cancel_l with (p := 2) by lia.
  replace (2 * (S n / 2)) with (2 * (S n / 2) + S n mod 2) by lia.
  rewrite <-Nat.div_mod by lia.
  replace (2 * S (n / 2)) with (2 * (n / 2 + 1)) by lia.
  rewrite Nat.mul_add_distr_l.
  replace (2 * (n / 2) + 2 * 1) with ((2 * (n / 2) + n mod 2) + 1) by lia.
  rewrite <-Nat.div_mod; lia.
Qed.

(* Function definition. *)

Function half_collatz (n : nat) {measure two_adic_valuation_S n}: list nat :=
  match (n mod 2) with
    | 0 => n :: nil
    | _ => n :: half_collatz (ht n)
  end.
Proof.
  intros n n' n_is_odd.
  rewrite <-ht_decreases_odd_two_adic_valuation_S_by_one with (n := n); lia.
Defined.

(* Checking some properties of the function. *)

Lemma half_collatz_is_not_nil:
  forall (n : nat),
  half_collatz n <> nil.
Proof.
  intros n; functional induction (half_collatz n); discriminate.
Qed.

Lemma half_collatz_head_is_param:
  forall (n : nat),
  head (half_collatz n) = Some n.
Proof.
  intros n; functional induction (half_collatz n); now simpl.
Qed.

Lemma half_collatz_last_is_even:
  forall (n : nat),
  (last (half_collatz n) 1) mod 2 = 0.
Proof.
  intros n; functional induction (half_collatz n).
  + now simpl last.
  + destruct_with_eqn (half_collatz (ht n)).
    - assert (half_collatz (ht n) <> nil) as Hnot_nil by apply half_collatz_is_not_nil.
      tauto.
    - now simpl last in *.
Qed.

Lemma half_collatz_trivial:
  forall (n : nat),
  n mod 2 = 0 ->
  half_collatz n = n :: nil.
Proof.
  intros n n_is_even; functional induction (half_collatz n).
  + auto.
  + now rewrite n_is_even in y.
Qed.

Lemma half_collatz_non_trivial_step:
  forall (n : nat),
  n mod 2 <> 0 ->
  half_collatz n = n :: (half_collatz (ht n)).
Proof.
  intros n n_is_odd; functional induction (half_collatz n); tauto.
Qed.

Lemma half_collatz_precise_length_bound:
  forall (n : nat),
  length (half_collatz n) = two_adic_valuation_S n + 1.
Proof.
  intros n; functional induction (half_collatz n).
  + unfold two_adic_valuation_S; rewrite two_adic_valuation_equation.
    replace (S n) with (n + 1) by lia; rewrite Nat.add_mod, e by lia.
    replace ((0 + 1 mod 2) mod 2) with 1; now compute.
  + rewrite ht_decreases_odd_two_adic_valuation_S_by_one in IHl.
    - simpl length; lia.
    - now destruct (n mod 2).
Qed.

Lemma two_adic_valuation_bound:
  forall (n : nat),
  two_adic_valuation n <= Nat.log2 n.
Proof.
  intros n; functional induction (two_adic_valuation n); try now compute; try lia.
  rewrite Nat.div_mod with (x := n) (y := 2) at 2 by lia.
  replace (2 * (n / 2) + n mod 2) with (2 * (n / 2)) by lia; rewrite Nat.log2_double; try lia.
  destruct (Nat.eq_dec n 0), (Nat.eq_dec n 1); try lia.
  + now replace n with 0 in y.
  + now replace n with 1 in e0.
  + apply Nat.div_str_pos; lia.
Qed.

Lemma half_collatz_log_bound:
  forall (n : nat),
  length (half_collatz n) <= Nat.log2 (S n) + 1.
Proof.
  intros n.
  rewrite half_collatz_precise_length_bound; unfold two_adic_valuation_S.
  cut (two_adic_valuation (S n) <= Nat.log2 (S n)); try lia.
  apply two_adic_valuation_bound.
Qed.