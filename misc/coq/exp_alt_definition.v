Require Import Psatz.
Require Import Reals.

Local Open Scope R_scope.


Definition expm := comp exp (mult_real_fct (-1) id).

Lemma expm_deriv:
  forall (x : R),
  derivable_pt_lim expm x (-expm x).
Proof.
  intros x.
  assert (-expm x = expm x * -1) as Hrw by lra; rewrite Hrw; clear Hrw.
  apply derivable_pt_lim_comp.
  + rewrite <-Rmult_1_r.
    apply derivable_pt_lim_scal, derivable_pt_lim_id.
  + unfold expm, mult_real_fct, id, comp; simpl.
    remember (-1 * x) as y.
    apply derivable_pt_lim_exp.
Qed.

Lemma deriv_prod:
  forall (f : R -> R),
  (forall (x : R), derivable_pt_lim f x (f x)) ->
  (forall (x : R),
   derivable_pt_lim (f * expm) x 0).
Proof.
  intros f Hderiv_f x.
  cut (derivable_pt_lim (f * expm) x (f x * expm x + f x * (-expm x))).
  + assert (f x * expm x + f x * - expm x = 0)  as Hrw by lra.
    rewrite Hrw; clear Hrw.
    auto.
  + apply derivable_pt_lim_mult.
    - apply Hderiv_f.
    - apply expm_deriv.
Qed.

Lemma prod_const:
  forall (f : R -> R),
  (forall (x : R), derivable_pt_lim f x (f x)) ->
  constant (f * expm)%F.
Proof.
  intros f Hderiv_f.
  assert (derivable (f * expm)) as Hderiv_prod.
  {
    apply derivable_mult.
    + unfold derivable, derivable_pt, derivable_pt_abs.
      intros x; exists (f x); auto.
    + unfold expm.
      apply derivable_comp.
      - apply derivable_scal, derivable_id.
      - apply derivable_exp.
  }
  apply null_derivative_1 with (pr := Hderiv_prod).
  intros x.
  apply derive_pt_eq_0.
  apply deriv_prod, Hderiv_f.
Qed.

Lemma expm_mult_exp:
  forall (x : R),
  expm x * exp x = 1.
Proof.
  intros x.
  unfold expm, comp, mult_real_fct, id.
  rewrite <-exp_plus.
  assert (-1 * x + x = 0) as Hrw by lra.
  rewrite Hrw; clear Hrw.
  apply exp_0.
Qed.

Theorem exp_alt_definition:
  forall (f : R -> R),
  (forall (x : R),
   derivable_pt_lim f x (f x)) ->
  exists (k : R),
  (forall (x : R),
   f x = k * exp x).
Proof.
  intros f Hderiv_f.
  exists (f 0).
  intros x.
  assert (forall (x : R), (f x) * (expm x) = f 0) as Hconst.
  {
    rewrite <-Rmult_1_r with (r := f 0).
    assert (1 = expm 0) as Hrw.
    {
      unfold expm, id, comp, mult_real_fct.
      rewrite Rmult_0_r, exp_0.
      auto.
    }
    rewrite Hrw; clear Hrw.
    cut (constant (f * expm)%F).
    + unfold constant, "*"%F; auto.
    + apply prod_const; auto.
  }
  rewrite <-Hconst with (x := x).
  rewrite Rmult_assoc, expm_mult_exp, Rmult_1_r.
  auto.
Qed.