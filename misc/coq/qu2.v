Require Import Psatz.
Require Import Reals.

Local Open Scope R.

Lemma zip: 0 <= 0 <= 1.
Proof. lra. Qed.

Inductive TwoPointLottery: Set :=
  | TPL (a b p : R) (r : 0 <= p <= 1)
  .

Definition SureLottery (a : R) := TPL a a 0 zip.

Definition ExpectedValue (f : R -> R) (L : TwoPointLottery) :=
  match L with
    | TPL a b p _ => p * (f a) + (1 - p) * (f b)
  end.

Definition Mean (L : TwoPointLottery) :=
  ExpectedValue (fun x => x) L.

Definition Var (L : TwoPointLottery) :=
  ExpectedValue (fun x => (x - (Mean L))^2) L.

Definition IsVNMUtility (U : TwoPointLottery -> R) :=
  forall (L : TwoPointLottery),
  U L = ExpectedValue (fun x => U (SureLottery x)) L.

Definition IsMeanVarianceUtilityWith (U : TwoPointLottery -> R) (u : R -> R -> R) :=
  forall (L : TwoPointLottery),
  IsVNMUtility U /\
  U L = u (Mean L) (Var L).

Definition IsMeanVarianceUtility (U : TwoPointLottery -> R) :=
  exists u, IsMeanVarianceUtilityWith U u.

Definition IsQuadraticMeanVariance (u : R -> R -> R) :=
  exists (a b c : R),
  forall (m : R) (v : nonnegreal),
  u m v = a * (m^2 + v) + b * m + c.

Definition IsQuadraticMeanVarianceUtility (U : TwoPointLottery -> R) :=
  exists u, IsMeanVarianceUtilityWith U u /\ IsQuadraticMeanVariance u.

(* We want to prove that
   forall U, IsMeanVarianceUtility U -> IsQuadraticMeanVarianceUtility U *)

Lemma mean_variance_sure:
  forall (U : TwoPointLottery -> R) (u : R -> R -> R),
  IsMeanVarianceUtilityWith U u ->
  forall (a : R),
  U (SureLottery a) = u a 0.
Proof.
  intros U u Hmvu a.
  unfold IsMeanVarianceUtilityWith in Hmvu.
  specialize (Hmvu (SureLottery a)).
  destruct Hmvu as [_ Hmvu].
  rewrite Hmvu.
  unfold SureLottery, Var, Mean, ExpectedValue.
  assert (0 * a + (1 - 0) * a = a) as Hrw by field.
  assert (0 * (a - (0 * a + (1 - 0) * a)) ^ 2 +
          (1 - 0) * (a - (0 * a + (1 - 0) * a)) ^ 2 = 0) as Hrw' by field.
  rewrite Hrw', Hrw; auto.
Qed.

Lemma mean_variance_family:
  forall (U : TwoPointLottery -> R) (u : R -> R -> R),
  IsMeanVarianceUtilityWith U u ->
  forall (a b p : R),
  0 <= p <= 1 ->
  u (p * a + (1 - p) * b) (p * (1 - p) * (b - a)^2) =
  p * (u a 0) + (1 - p) * (u b 0).
Proof.
  intros U u Hmvu a b p c.
  pose (TPL a b p c) as L.
  pose (Hmvu L) as HmvuL.
  unfold IsMeanVarianceUtilityWith in HmvuL.
  destruct HmvuL as [HVNMU HmvuL].
  assert (Mean L = p * a + (1 - p) * b) as Hrw
    by (unfold Mean, ExpectedValue; compute; field).
  rewrite Hrw in HmvuL; clear Hrw.
  assert (Var L = p * (1 - p) * (b - a)^2) as Hrw
    by (unfold Var, ExpectedValue; compute; field).
  rewrite Hrw in HmvuL; clear Hrw.
  rewrite <-HmvuL.
  unfold IsVNMUtility in HVNMU.
  specialize (HVNMU L).
  rewrite HVNMU.
  simpl ExpectedValue.
  repeat rewrite mean_variance_sure with (u := u) by auto.
  auto.
Qed.

Lemma neg_sqr_bound:
  forall (x a : R),
  0 <= a ->
  x <= -a ->
  a^2 <= x^2.
Proof.
  intros x a Hpos_a Hubound_a.
  rewrite <-pow2_abs with (x := x).
  apply pow_incr; rewrite Rabs_left1; lra.
Qed.

Lemma sqr_one_abs_bound:
  forall (a : R),
  1 <= Rabs a ->
  1 <= a^2.
Proof.
  intros a Hbound.
  rewrite <-Rsqr_pow2, Rsqr_abs.
  assert (1 = Rsqr 1) as Hrw by (compute; field); rewrite Hrw; clear Hrw.
  apply Rsqr_incr_1; lra.
Qed.

Lemma abs_le_implies_le:
  forall (a b : R),
  0 <= b ->
  Rabs a <= b ->
  a <= b.
Proof.
  intros a b Hpos_b Hbound_abs_a.
  destruct (Rlt_dec a 0).
  + lra.
  + rewrite Rabs_right in Hbound_abs_a; lra.
Qed.

Lemma pq_bounds:
  forall (a m p q: R),
  (m <= a - 1) \/ (m >= a + 1) ->
  p = ((m - a) - 1) / (2 * (m - a)) ->
  q = 1 / (m - a)^2 ->
  0 <= p <= 1 /\ 0 < q <= 1.
Proof.
  intros a m p q Hbound_m Heq_p Heq_q.
  cut (0 <= Rabs (m - a - 1) <= 2 * Rabs (m - a) /\
       1 <= Rabs (m - a)).
  + intros [[Hlbound_ma1 Hubound_ma1] Hlbound_ma].
    assert (1 <= (m - a)^2) as Hbound_ma_sq by (apply sqr_one_abs_bound; lra).
    rewrite Heq_q, Heq_p; repeat split.
    - destruct Hbound_m as [Hubound | Hlbound]; unfold Rdiv.
      * repeat rewrite Rabs_left1 in * by lra.
        rewrite <-Rmult_opp_opp.
        apply Rmult_le_pos; try lra.
        rewrite Ropp_inv_permute by lra.
        apply Rlt_le, Rinv_0_lt_compat; lra.
      * apply Rmult_le_pos; try lra.
        apply Rlt_le, Rinv_0_lt_compat; lra.
    - apply abs_le_implies_le; try lra.
      unfold Rdiv; rewrite Rabs_mult, Rabs_Rinv, Rabs_mult by lra.
      rewrite Rabs_right with (r := 2) by lra.
      rewrite <-Rinv_r with (r := 2 * Rabs (m - a)) at 4 by lra.
      apply Rmult_le_compat_r; auto.
      apply Rlt_le, Rinv_0_lt_compat; lra.
    - apply Rdiv_lt_0_compat; try lra.
    - unfold Rdiv; rewrite Rmult_1_l, <-Rinv_1.
      apply Rle_Rinv; lra.
  + destruct Hbound_m.
    - repeat rewrite Rabs_left1; lra.
    - repeat rewrite Rabs_right; lra.
Qed.

Lemma sure_outcomes_outside:
  forall (U : TwoPointLottery -> R) (u : R -> R -> R),
  IsMeanVarianceUtilityWith U u ->
  forall (a m : R),
  (m <= a - 1) \/ (m >= a + 1) ->
  (u m 0) = ((m - a) * (m - a - 1) / 2) * (u (a - 1) 0) -
            (m - a - 1) * (m - a + 1) * (u a 0) +
            ((m - a) * (m - a + 1) / 2) * (u (a + 1) 0).
Proof.
  intros U u Hmvu a m Hbounds_m.
  remember (((m - a) - 1)/(2*(m - a))) as p.
  pose (mean_variance_family U u Hmvu (a-1) (a+1) p) as Hc1m1.
  remember (1/(m - a)^2) as q.
  pose (mean_variance_family U u Hmvu m a q) as Hcma.
  pose (pq_bounds a m p q Hbounds_m Heqp Heqq) as Haux_pq.
  destruct Haux_pq as [Hbounds_p Hbounds_q].
  assert (0 <= q <= 1) as Hbounds_q_rel by lra.
  specialize (Hc1m1 Hbounds_p).
  specialize (Hcma Hbounds_q_rel).
  assert (p * (a - 1) + (1 - p) * (a + 1) = q * m + (1 - q) * a) as Heq_mean
    by (rewrite Heqp, Heqq; field; lra).
  assert (p * (1 - p) * (a + 1 - (a - 1)) ^ 2 = q * (1 - q) * (a - m) ^ 2) as Heq_var
    by (rewrite Heqp, Heqq; field; lra).
  assert (p * u (a-1) 0 + (1 - p) * u (a+1) 0 = q * u m 0 + (1 - q) * u a 0) as Heq_main
    by (rewrite <-Hc1m1, <-Hcma, Heq_mean, Heq_var; auto).
  assert (q * u m 0 = p * u (a-1) 0 + (1 - p) * u (a+1) 0 - (1 - q) * u a 0) as Heq_main' by lra.
  apply Rmult_eq_compat_l with (r := 1 / q) in Heq_main'.
  assert (1 / q * (q * u m 0) = u m 0) as Hrw by (field; lra).
  rewrite Hrw in Heq_main'.
  rewrite Heq_main', Heqp, Heqq.
  field; lra.
Qed.

Lemma sure_outcomes_outside_std:
  forall (U : TwoPointLottery -> R) (u : R -> R -> R),
  IsMeanVarianceUtilityWith U u ->
  exists (a b c : R),
  forall (m : R),
  m <= -1 \/ m >= 1 ->
  (u m 0) = a * m^2 + b * m + c.
Proof.
  intros U u Hmvu.
  exists ((u (-1) 0) / 2 - (u 0 0) + (u 1 0) / 2). (* (a/2 - b/2 + c/2) - c + (a/2 + b/2 + c/2) *)
  exists ((u 1 0) / 2 - (u (-1) 0) / 2).           (* (a/2 + b/2 + c/2) - (a/2 - b/2 + c/2) *)
  exists (u 0 0).
  intros m Hbounds_m; rewrite sure_outcomes_outside with (U := U) (u := u) (a := 0); auto.
  + assert (m - 0 = m) as Hrw by lra; rewrite Hrw; clear Hrw.
    assert (0 - 1 = -1) as Hrw by lra; rewrite Hrw; clear Hrw.
    assert (0 + 1 = 1) as Hrw by lra; rewrite Hrw; clear Hrw.
    field.
  + assert (0 - 1 = -1) as Hrw by lra; rewrite Hrw; clear Hrw.
    assert (0 + 1 = 1) as Hrw by lra; rewrite Hrw; clear Hrw.
    auto.
Qed.

Lemma sure_outcomes:
  forall (U : TwoPointLottery -> R) (u : R -> R -> R),
  IsMeanVarianceUtilityWith U u ->
  exists (a b c : R),
  forall (m : R),
  (u m 0) = a * m^2 + b * m + c.
Proof.
  intros U u Hmvu; pose (sure_outcomes_outside_std U u Hmvu) as Hout.
  destruct Hout as [a [b [c Hout]]].
  exists a, b, c; intros m.
  destruct (Rle_dec m (-1)), (Rge_dec m 1); try lra; try (apply Hout; lra).
  rewrite sure_outcomes_outside with (U := U) (u := u) (a := 2) by (auto; lra).
  repeat rewrite Hout by lra.
  field.
Qed.

Lemma all_outcomes:
  forall (U : TwoPointLottery -> R) (u : R -> R -> R),
  IsMeanVarianceUtilityWith U u ->
  exists (a b c : R),
  forall (m : R) (v : nonnegreal),
  (u m v) = a * (m^2 + v) + b * m + c.
Proof.
  intros U u Hmvu.
  pose (sure_outcomes U u Hmvu) as Hu_sure.
  destruct Hu_sure as [a [b [c Hu_sure]]].
  exists a, b, c; intros m v.
  assert (0 <= 1/2 <= 1) as Hhip by lra.
  pose (mean_variance_family U u Hmvu
                             (m - Rsqrt v) (m + Rsqrt v) (1/2) Hhip) as Hmvf.
  assert (1/2 * (m - Rsqrt v) + (1 - 1/2) * (m + Rsqrt v) = m) as Hrw by field.
  rewrite Hrw in Hmvf; clear Hrw.
  assert (1/2 * (1 - 1/2) * (m + Rsqrt v - (m - Rsqrt v))^2 =
         (Rsqrt v) * (Rsqrt v)) as Hrw by field.
  rewrite Hrw, Rsqrt_Rsqrt in Hmvf; clear Hrw.
  rewrite Hmvf.
  rewrite <-Rsqrt_Rsqrt with (x := v).
  pose (Hu_sure (m - Rsqrt v)) as Hrw.
  rewrite Hrw; clear Hrw.
  pose (Hu_sure (m + Rsqrt v)) as Hrw.
  rewrite Hrw; clear Hrw.
  field.
Qed.

Theorem mean_variance_implies_quadratic:
  forall U, 
  IsMeanVarianceUtility U -> 
  IsQuadraticMeanVarianceUtility U.
Proof.
  intros U Hmv; unfold IsMeanVarianceUtility, IsQuadraticMeanVarianceUtility in *.
  destruct Hmv as [u Hmvu].
  exists u; split; auto.
  unfold IsQuadraticMeanVariance.
  exact (all_outcomes U u Hmvu).
Qed. 
