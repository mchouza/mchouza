Require Import Factorial.
Require Import NArith NGcd Znat.
Require Import Omega.

Local Open Scope N_scope.

Lemma recursion_eq {A}:
  forall (b : A) (f f' : N -> A -> A) (n : N),
  (forall a k, k <= n -> (f k a) = (f' k a)) ->
  N.recursion b f n = N.recursion b f' n.
Proof.
  intros b f f' n.
  N.induct n.
  {
    intros _; repeat rewrite N.recursion_0; auto.
  }
  {
    intros n Hind Hf_pw_eq.
    repeat rewrite N.recursion_succ by Morphisms.solve_proper.
    cut (N.recursion b f n = N.recursion b f' n).
    + intros Hrec_eq; rewrite Hrec_eq.
      apply Hf_pw_eq.
      apply N.le_succ_diag_r.
    + apply Hind.
      intros a k Hk_le_n.
      apply Hf_pw_eq.
      apply N.le_trans with (m := n); auto.
      apply N.le_succ_diag_r.
  }
Qed.

Lemma n_sub_mod_is_div:
  forall n d,
  d <> 0 ->
  (d | n - n mod d).
Proof.
  intros n d Hd_ne_0.
  rewrite N.div_mod with (a := n) (b := d) at 1 by auto.
  rewrite N.add_sub.
  apply N.divide_factor_l.
Qed.

Lemma div_mult_compat:
  forall a b m n,
  (a | m) ->
  (b | n) ->
  (a * b | m * n).
Proof.
  intros a b m n.
  unfold N.divide.
  intros [r' Hm_div] [r'' Hn_div].
  exists (r' * r'').
  rewrite Hm_div, Hn_div.
  rewrite <-N.mul_assoc with (n := r') (m := a).
  rewrite N.mul_comm with (n := a) (m := r'' * b).
  rewrite N.mul_comm with (n := a) (m := b).
  repeat rewrite N.mul_assoc; auto.
Qed.

Lemma div_sub:
  forall a b,
  b <> 0 ->
  b <= a ->
  (a - b) / b = a/b - 1.
Proof.
  intros a b Hb_nz Hb_le_a.
  SearchAbout (_ - _ = _).
  apply eq_sym, N.add_sub_eq_r.
  apply Nmult_reg_r with (p := b), Nplus_reg_l with (n := (a - b) mod b); auto.
  rewrite N.add_comm, N.mul_comm, <-N.div_mod by auto.
  rewrite N.mul_sub_distr_r, N.mul_1_l.
  SearchAbout ((_-_)*_).

Definition NFallPow x n :=
  N.recursion 1 (fun k r => r * (x - (n - k) + 1)) n.

Definition NFact n := NFallPow n n.

Lemma fall_pow_1st_0_eq_1:
  forall k,
  NFallPow 0 k = 1.
Proof.
  intros k.
  N.induct k.
  + simpl; auto.
  + intros k Hind.
    unfold NFallPow in *.
    rewrite N.recursion_succ by Morphisms.solve_proper.
    rewrite N.sub_0_l, N.add_0_l, N.mul_1_r.
    rewrite <-Hind at 2.
    apply recursion_eq; intros a k' Hk_bound.
    repeat rewrite N.sub_0_l, N.add_0_l; auto.
Qed.

Lemma fall_pow_2nd_0_eq_1:
  forall n,
  NFallPow n 0 = 1.
Proof.
  compute; auto.
Qed.

Lemma fall_pow_2nd_1_eq_1st:
  forall n,
  1 <= n ->
  NFallPow n 1 = n.
Proof.
  intros.
  rewrite N.one_succ; unfold NFallPow; rewrite N.recursion_succ by Morphisms.solve_proper.
  rewrite N.recursion_0, <-N.one_succ, N.sub_0_r, N.sub_add, N.mul_1_l; auto.
Qed.  

Lemma fall_pow_join:
  forall n k d,
  NFallPow (n + d) (k + d) = NFallPow (n + d) d * NFallPow n k.
Proof.
  intros n k d.
  N.induct d.
  {
    repeat rewrite N.add_0_r; rewrite fall_pow_2nd_0_eq_1.
    rewrite N.mul_1_l; auto.
  }
  {
    intros d Hind.
    unfold NFallPow in *.
    rewrite N.add_succ_r with (n := k).
    repeat (rewrite N.recursion_succ by Morphisms.solve_proper; auto).
    repeat rewrite N.sub_succ_l, N.sub_diag by apply N.le_refl.
    rewrite <-N.mul_assoc.
    rewrite N.mul_comm with (n := (n + N.succ d - N.succ 0 + 1)).
    rewrite N.mul_assoc.
    apply N.mul_cancel_r; try (rewrite N.add_1_r; apply N.neq_succ_0).
    assert (N.recursion 1 (fun k0 r : N => r * (n + d - (k + d - k0) + 1)) (k + d) =
            N.recursion 1 (fun k0 r : N => r * (n + N.succ d - (N.succ (k + d) - k0) + 1)) (k + d))
           as Hlhs_eq.
    {
      apply recursion_eq.
      intros a k' Hbound.
      rewrite N.sub_succ_l, N.add_succ_r, N.sub_succ; auto.
    }
    assert (N.recursion 1 (fun k r : N => r * (n + d - (d - k) + 1)) d =
            N.recursion 1 (fun k0 r : N => r * (n + N.succ d - (N.succ d - k0) + 1)) d) as Hrhs_eq.
    {
      apply recursion_eq.
      intros a k' Hbound.
      rewrite N.sub_succ_l, N.add_succ_r, N.sub_succ; auto.
    }
    rewrite <-Hlhs_eq, <-Hrhs_eq.
    apply Hind.
  }
Qed.

Lemma fall_pow_nz_normal:
  forall n k,
  k <= n ->
  NFallPow n k <> 0.
Proof.
  intros n k Hbound.
  assert (exists d, n = d + k) as [d Hd_eq] by
    (exists (n - k); rewrite N.sub_add; auto).
  subst n; clear Hbound.
  N.induct k.
  {
    compute; discriminate.
  }
  {
    unfold NFallPow.
    intros k Hind.
    rewrite N.recursion_succ by Morphisms.solve_proper; auto.
    rewrite N.sub_succ_l with (n := k) by apply N.le_refl.
    apply N.neq_mul_0; split.
    + assert (N.recursion 1 (fun k0 r : N => r * (d + k - (k - k0) + 1)) k =
              N.recursion 1 (fun k0 r : N => r * (d + N.succ k - (N.succ k - k0) + 1)) k) as Hrec_eq.
      {
        apply recursion_eq; intros a k' Hk_bound.
        rewrite N.sub_succ_l, N.add_succ_r, N.sub_succ; auto.
      }
      rewrite <-Hrec_eq; apply Hind.
    + rewrite N.add_1_r; apply N.neq_succ_0.
  }
Qed.

Lemma fall_pow_nz:
  forall n k,
  NFallPow n k <> 0.
Proof.
  intros n k.
  destruct (N.le_gt_cases k n).
  + apply fall_pow_nz_normal; auto.
  + remember (k - n) as d.
    assert (k = d + n) as Hk_def.
    {
      rewrite Heqd, N.sub_add; auto.
      apply N.lt_le_incl; auto.
    }
    rewrite <-N.add_0_l with (n := n), Hk_def, fall_pow_join.
    rewrite N.add_0_l; apply N.neq_mul_0; split.
    - apply fall_pow_nz_normal; reflexivity.
    - rewrite fall_pow_1st_0_eq_1; discriminate.
Qed.

Lemma fact_fall_pow:
  forall n d,
  NFact (n + d) = NFallPow (n + d) d * NFact n.
Proof.
  unfold NFact; intros; apply fall_pow_join with (k := n).
Qed.

Lemma fact_nz:
  forall n,
  NFact n <> 0.
Proof.
  unfold NFact; intros; apply fall_pow_nz with (k := n).
Qed.

Lemma fall_pow_div_if_long:
  forall n k d,
  k <= n ->
  0 < d <= k ->
  (d | NFallPow n k).
Proof.
  intros n k d Hk_bound Hd_bound.
  assert (d <> 0) as Hd_ne_0 by apply N.neq_sym, N.lt_neq, Hd_bound.
  assert (1 <= k - n mod d) as Hksub_bound.
  {
    apply N.le_add_le_sub_r, N.lt_pred_le.
    rewrite <-N.add_pred_l by discriminate; simpl.
    apply N.lt_le_trans with (m := d).
    + apply N.mod_lt; auto.
    + apply Hd_bound.
  }
  assert (1 <= n - n mod d) as Hnsub_bound by
    (apply N.le_trans with (m := k - n mod d); auto; apply N.sub_le_mono_r; auto).
  rewrite <-N.sub_add with (m := n) (n := n mod d) by (apply N.mod_le; auto).
  rewrite <-N.sub_add with (m := k) (n := n mod d) by
    (apply N.lt_le_incl, N.lt_le_trans with (m := d); try apply N.mod_lt; auto; apply Hd_bound).
  rewrite fall_pow_join.
  rewrite N.sub_add by (apply N.mod_le; auto).
  rewrite <-N.sub_add with (m := n - n mod d) (n := 1) by apply Hnsub_bound.
  rewrite <-N.sub_add with (m := k - n mod d) (n := 1) by apply Hksub_bound.
  rewrite fall_pow_join.
  rewrite fall_pow_2nd_1_eq_1st by
    (rewrite N.add_comm; apply N.le_add_r).
  rewrite N.sub_add by apply Hnsub_bound.
  rewrite N.mul_comm.
  repeat apply N.divide_mul_l.
  apply n_sub_mod_is_div; auto.
Qed.

Lemma div_fact:
  forall n k,
  k > 0 ->
  exists m,
  NFact n = m * k^(n / k).
Proof.
  intros n k Hk_bound.
  exists (NFact n / k^(n / k)).
  rewrite N.mul_comm.
  assert (k <> 0) as Hk_ne_0 by apply N.neq_sym, N.lt_neq, N.gt_lt, Hk_bound.
  assert (k ^ (n / k) <> 0) as Hpow_k_bound by 
    (apply N.pow_nonzero; auto).
  apply N.div_exact; auto.
  apply N.mod_divide; auto.
  remember (n / k) as q.
  revert n Heqq Hpow_k_bound.
  N.induct q.
  + intros n _ _; rewrite N.pow_0_r; apply N.divide_1_l.
  + unfold NFact; intros q Hind n' Hq_def Hk_pow_bound.
    assert (k <= n') as Hk_le_n'.
    {
      apply N.div_str_pos_iff; auto.
      rewrite <-Hq_def.
      apply N.lt_0_succ.
    }
    rewrite N.pow_succ_r by apply N.le_0_l.
    rewrite <-N.sub_add with (m := n') (n := k) by auto.
    rewrite fall_pow_join, N.sub_add by auto.
    apply div_mult_compat.
    - apply fall_pow_div_if_long; auto.
      split; try reflexivity.
      apply N.gt_lt; auto.
    - apply Hind.
      SearchAbout ((_ - _) / _).
      * admit.
      * apply N.pow_nonzero, not_eq_sym, N.lt_neq, N.gt_lt, Hk_bound.
Admitted.

Lemma gcd_nz:
  forall a b,
  a <> 0 ->
  b <> 0 ->
  N.gcd a b <> 0.
Proof.
  intros a b Hcond_a Hcond_b.
  destruct (N.eq_dec (N.gcd a b) 0); auto.
  cut (a = 0); auto; apply N.gcd_eq_0_l with (m := b); auto.
Qed.

Lemma gcd_is_gcd:
  forall a b c,
  a <> 0 ->
  b <> 0 ->
  (c | a) ->
  (c | b) ->
  c <= N.gcd a b.
Proof.
  intros a b c Hcond_a Hcond_b Hc_div_a Hc_div_b.
  apply N.divide_pos_le.
  + cut (N.gcd a b <> 0).
    - destruct (N.gcd a b).
      * tauto.
      * intros; compute; auto.
    - apply gcd_nz; auto.
  + apply N.gcd_greatest; auto.
Qed.

Lemma cd_rel_prime_1:
  forall a b c,
  a <> 0 ->
  b <> 0 ->
  (c | a) ->
  (c | b) ->
  N.gcd a b = 1 ->
  c = 1.
Proof.
  intros a b c Hcond_a Hcond_b Hc_div_a Hc_div_b Hgcd_a_b.
  destruct (N.zero_one c) as [Hc_0 | [Hc_1 | Hc_gt_1]].
  + absurd (a = 0); auto.
    apply N.divide_0_l.
    rewrite <-Hc_0; auto.
  + auto.
  + absurd (c <= 1).
    - apply N.lt_nge; auto.
    - rewrite <-Hgcd_a_b; apply gcd_is_gcd; auto.
Qed.

Lemma rel_prime_prod:
  forall a b c,
  a <> 0 ->
  b <> 0 ->
  c <> 0 ->
  N.gcd a b = 1 ->
  N.gcd a c = 1 ->
  N.gcd a (b * c) = 1.
Proof.
  intros a b c Hcond_a Hcond_b Hcond_c Hgcd_a_b Hgcd_a_c.
  destruct (N.zero_one (N.gcd a (b * c))) as [Hgcd_0 | [Hgcd_1 | Hhcd_gt_1]].
  {
    absurd (N.gcd a (b * c) = 0); auto. 
    apply gcd_nz; auto; apply N.neq_mul_0; auto.
  }
  {
    auto.
  }
  {  
    absurd (N.gcd (N.gcd a (b * c)) c = 1).
    + apply N.neq_sym, N.lt_neq.
      cut (N.gcd (N.gcd a (b * c)) c = N.gcd a (b * c)).
      - intros Hgcd_rec; rewrite Hgcd_rec; auto.
      - apply N.divide_gcd_iff; try apply N.gcd_nonneg.
        apply N.gauss with (m := b); try apply N.gcd_divide_r.
        apply cd_rel_prime_1 with (a := a) (b := b); auto.
        * apply N.divide_trans with (m := N.gcd a (b * c));
          apply N.gcd_divide_l.
        * apply N.gcd_divide_r.
    + apply cd_rel_prime_1 with (a := a) (b := c); auto.
      - apply N.divide_trans with (m := N.gcd a (b * c));
        apply N.gcd_divide_l.
      - apply N.gcd_divide_r.
  }
Qed.

Lemma gcd_pow_nz:
  forall a b k,
  a <> 0 -> b <> 0 ->
  N.gcd a b = 1 ->
  N.gcd a (b^k) = 1.
Proof.
  N.induct k.
  {
    intros Hbound_a Hbound_b Hgcd; rewrite N.pow_0_r.
    apply N.gcd_1_r.
  }
  {
    intros n Hind Hbound_a Hbound_b Hgcd.
    specialize (Hind Hbound_a Hbound_b Hgcd).
    rewrite N.pow_succ_r by apply N.le_0_l.
    apply rel_prime_prod; auto.
    apply N.pow_nonzero; auto.
  }
Qed.

Lemma gcd_pow:
  forall a b k,
  a <> 0 ->
  N.gcd a b = 1 ->
  N.gcd a (b^k) = 1.
Proof.
  intros a b k Hcond_a.
  destruct (N.eq_dec k 0) as [Hcond_k | Hcond_k].
  + rewrite Hcond_k, N.pow_0_r, N.gcd_1_r; auto.
  + destruct (N.eq_dec b 0) as [Hcond_b | Hcond_b].
    - rewrite Hcond_b, N.pow_0_l; auto.
    - apply gcd_pow_nz; auto.
Qed.

Lemma div_coeff_pow:
  forall a b j k m n,
  a <> 0 ->
  N.gcd a b = 1 ->
  j * a^N.succ m = k * b^n ->
  j * a^m = (k/a) * b^n.
Proof.
  intros a b j k m n Hcond_a Hgcd Hbase.
  cut (a | k).
  + intros Hdiv_k.
    assert (N.gcd a k = a) as Hgcd_a_k by
      (apply N.divide_gcd_iff with (n := a) (m := k); try apply N.le_0_l; auto).
    rewrite <-N.mul_cancel_l with (p := a) by auto.
    repeat rewrite N.mul_assoc. rewrite N.mul_comm with (m := k/a).
    rewrite <-Hgcd_a_k at 3. rewrite N.gcd_comm. 
    rewrite N.lcm_equiv2 by (rewrite N.gcd_comm; rewrite Hgcd_a_k; auto).
    rewrite <-N.lcm_equiv1 by (rewrite N.gcd_comm; rewrite Hgcd_a_k; auto).
    rewrite N.gcd_comm, Hgcd_a_k, N.div_same, N.mul_1_r by auto.
    rewrite <-N.mul_assoc, N.mul_comm, <-N.mul_assoc, N.mul_comm with (m := a).
    rewrite <-N.pow_succ_r by apply N.le_0_l; auto.
  + apply N.gauss with (m := b^n).
    - rewrite N.mul_comm, <-Hbase, N.pow_succ_r by apply N.le_0_l.
      rewrite N.mul_comm.
      repeat apply N.divide_mul_l; apply N.divide_refl.
    - apply gcd_pow; auto.
Qed.

Lemma div_prod_pow_rel_prime:
  forall a b m n j k,
  a <> 0->
  j * a^m = k * b^n /\ N.gcd a b = 1 ->
  exists p,
  p * a^m * b^n = j * a^m.
Proof.
  intros a b m; revert a b.
  N.induct m.
  {
    intros a b n j k Hcond_a [Hind Hgcd].
    exists k.
    rewrite N.pow_0_r in *; repeat rewrite N.mul_1_r in *.
    auto.
  }
  {
    intros m Hind a b n j k Hcond_a [Hbase Hgcd].
    specialize (Hind a b n j (k / a)).
    assert (j * a ^ m = (k / a) * b ^ n) as Hbase_div by
      (apply div_coeff_pow; auto).
    assert (j * a ^ m = k / a * b ^ n /\ N.gcd a b = 1) as Haux by (split; auto).
    specialize (Hind Hcond_a (conj Hbase_div Hgcd)).
    destruct Hind as [p Hp].
    exists p.
    rewrite N.pow_succ_r by apply N.le_0_l.
    rewrite N.mul_comm with (n := p).
    rewrite N.mul_comm with (n := j).
    repeat rewrite <-N.mul_assoc.
    destruct (N.eq_dec a 0).
    + rewrite e; repeat rewrite N.mul_0_l; auto.
    + apply N.mul_cancel_l; auto.
      rewrite N.mul_assoc, N.mul_comm with (m := p), N.mul_comm with (m := j).
      auto.
  }
Qed.

Theorem zeros_at_end_1:
  forall n,
  exists m,
  NFact n = m * 10^(n/5).
Proof.
  intros n.
  assert (exists m', NFact n = m' * 2^(n / 2)) as [m' Hdiv2]
    by (apply div_fact; apply N2Z.inj_gt; simpl; omega).
  assert (exists m'', NFact n = m'' * 5^(n / 5)) as [m'' Hdiv5]
    by (apply div_fact; apply N2Z.inj_gt; simpl; omega).
  assert (exists m''', m''' * 2^(n / 2) * 5^(n / 5) = m' * 2^(n / 2))
    as [m''' Hdiv2n5].
  {
    apply div_prod_pow_rel_prime with (k := m''); try discriminate; split.
    + rewrite <-Hdiv2, <-Hdiv5; auto.
    + compute; auto.
  }
  exists (m''' * 2^(n/2-n/5)).
  rewrite Hdiv2, <-Hdiv2n5.
  assert (m''' <> 0) as Hnz.
  {
    destruct m'''.
    + rewrite N.mul_0_l, <-Hdiv2 in Hdiv2n5.
      exfalso; apply fact_nz with (n := n); auto.
    + discriminate.
  }
  repeat rewrite <-N.mul_assoc.
  apply N.mul_cancel_l with (p := m'''); auto.
  assert (2 * 5 = 10) as H2by5 by (compute; auto).
  rewrite <-H2by5, N.pow_mul_l, N.mul_assoc.
  apply N.mul_cancel_r.
  + apply N.pow_nonzero; discriminate.
  + rewrite <-N.pow_add_r, N.sub_add; auto.
    apply N.div_le_compat_l; split.
    - apply N.lt_0_2.
    - apply N2Z.inj_le; simpl; omega.
Qed.