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

Lemma sure_outcomes_outside:
  forall (U : TwoPointLottery -> R) (u : R -> R -> R),
  IsMeanVarianceUtilityWith U u ->
  forall (a m : R),
  (m < a - 1) \/ (m > a + 1) ->
  (u m 0) = ((m - a) * (m - a - 1) / 2) * (u (a - 1) 0) -
            (m - a - 1) * (m - a + 1) * (u a 0) +
            ((m - a) * (m - a + 1) / 2) * (u (a + 1) 0).
Proof.
Admitted.

Lemma sure_outcomes:
  forall (U : TwoPointLottery -> R) (u : R -> R -> R),
  IsMeanVarianceUtilityWith U u ->
  exists (a b c : R),
  forall (m : R),
  (u m 0) = a * m^2 + b * m + c.
Proof.
Admitted.

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