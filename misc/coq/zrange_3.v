Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Recdef.
Require Import ZArith.
Require Import Znumtheory.

Local Open Scope Z.

Set Implicit Arguments.

Lemma Zlength_ge_0 {A : Type}:
  forall (l : list A),
  0 <= Zlength l.
Proof.
  induction l as [|h t].
  + now compute.
  + rewrite Zlength_cons; omega.
Qed.

Function Zrange_stride (s n k : Z) {measure Zabs_nat n} : list Z :=
  if 0 <? n then
    s :: (Zrange_stride (s + k) (n - 1) k)
  else
    nil.
Proof.
  intros _ n _ n_gt_0.
  apply Z.ltb_lt in n_gt_0.
  apply Zabs_nat_lt; omega.
Defined.

Definition Zrange (s n : Z) : list Z :=
  Zrange_stride s n 1.

Lemma Zrange_stride_empty:
  forall (s n k : Z),
  n <= 0 ->
  Zrange_stride s n k = nil.
Proof.
  intros s n k n_le_0; unfold Zrange.
  functional induction (Zrange_stride s n k).
  + apply Z.ltb_lt in e; omega.
  + auto.
Qed.

Lemma Zrange_stride_cons:
  forall (s n k : Z),
  0 < n ->
  Zrange_stride s n k = s :: Zrange_stride (s + k) (n - 1) k.
Proof.
  intros s n k n_gt_0.
  functional induction (Zrange_stride s n k).
  + auto.
  + apply Z.ltb_ge in e; omega.
Qed.

Lemma Zrange_cons:
  forall (s n : Z),
  0 < n ->
  Zrange s n = s :: Zrange (s + 1) (n - 1).
Proof.
  intros s n n_gt_0; unfold Zrange.
  apply Zrange_stride_cons; omega.
Qed.

Lemma Zrange_empty:
  forall (s n : Z),
  n <= 0 ->
  Zrange s n = nil.
Proof.
  intros s n n_le_0; unfold Zrange.
  now rewrite Zrange_stride_empty by omega.
Qed.

Lemma Zrange_length:
  forall (s n : Z),
  0 <= n ->
  Zlength (Zrange s n) = n.
Proof.
  intros s n n_ge_0; revert s.
  apply Zlt_0_ind with (x := n); auto; clear n n_ge_0.
  intros n Hind n_ge_0 s.
  destruct (Z_eq_dec n 0) as [n_eq_0 | n_ne_0].
  + subst; now rewrite Zrange_empty by omega.
  + rewrite Zrange_cons, Zlength_cons, Hind; omega.
Qed.

Lemma Zrange_app:
  forall (s n n' : Z),
  0 <= n ->
  0 <= n' ->
  Zrange s (n + n') = (Zrange s n) ++ (Zrange (s + n) n').
Proof.
  intros s n n' n_ge_0 n'_ge_0.
  remember (s + n) as m.
  assert (s = m - n) as Hrw by omega; rewrite Hrw; clear Hrw s Heqm.
  generalize n_ge_0; apply Zlt_0_ind with (x := n); auto; clear n n_ge_0.
  intros n Hind _ n_gt_0.
  destruct (Z.eq_dec n 0) as [n_eq_0 | n_ne_0].
  + subst; rewrite Z.sub_0_r, Z.add_0_l.
    now rewrite Zrange_empty with (n := 0), app_nil_l by omega.
  + rewrite Zrange_cons with (n := n + n') by omega.
    rewrite Zrange_cons with (n := n) by omega.
    rewrite <-app_comm_cons; apply f_equal.
    assert (m - n + 1 = m - (n - 1)) as Hrw by omega; rewrite Hrw; clear Hrw.
    assert (n + n' - 1 = (n - 1) + n') as Hrw by omega; rewrite Hrw; clear Hrw.
    destruct (Z.eq_dec (n - 1) 0) as [nm1_eq_0 | nm1_ne_0].
    - rewrite nm1_eq_0, Zrange_empty with (n := 0) by omega.
      simpl; now rewrite Z.sub_0_r.
    - now rewrite Hind by omega.
Qed.

Fixpoint sum_list (l : list Z) : Z :=
  match l with
    | h :: t => h + sum_list t
    | nil => 0
  end.

Fixpoint prod_list (l : list Z) : Z :=
  match l with
    | h :: t => h * prod_list t
    | nil => 1
  end.

Lemma prod_list_app:
  forall (l l' : list Z),
  prod_list (l ++ l') = (prod_list l) * (prod_list l').
Proof.
  induction l as [|h t]; intros l'.
  + rewrite app_nil_l; simpl prod_list; ring.
  + rewrite <-app_comm_cons; simpl prod_list; rewrite IHt; ring.
Qed.

Function Zfact (n : Z) {measure Zabs_nat n} : Z :=
  if 0 <? n then
    n * Zfact (n - 1)
  else
    1.
Proof.
  intros n n_gt_0.
  apply Z.ltb_lt in n_gt_0.
  apply Zabs_nat_lt; omega.
Defined.

Lemma Zfact_works:
  forall (n : Z),
  0 <= n ->
  Zfact n = Z.of_nat (fact (Z.to_nat n)).
Proof.
  intros n n_ge_0.
  functional induction (Zfact n).
  + apply Z.ltb_lt in e.
    assert (Z.to_nat n = S (Z.to_nat (n - 1))) as Hrw.
    {
      rewrite <-Z2Nat.inj_succ by omega.
      assert (Z.succ (n - 1) = n) as Hrw by omega; now rewrite Hrw.
    }
    rewrite Hrw; unfold fact; fold fact.
    rewrite Nat2Z.inj_mul, IHz by omega.
    now rewrite <-Hrw, Z2Nat.id by omega.
  + apply Z.ltb_ge in e.
    assert (n = 0) as Hrw by omega; now subst.
Qed.

Lemma Zfact_is_prod_list:
  forall (n : Z),
  Zfact n = prod_list (Zrange 1 n).
Proof.
  intros n; functional induction (Zfact n).
  + assert (n = (n - 1) + 1) as Hrw by omega; rewrite Hrw at 3; clear Hrw.
    apply Z.ltb_lt in e.
    rewrite Zrange_app with (n := n - 1) (n' := 1) by omega.
    rewrite IHz, prod_list_app.
    rewrite Zrange_cons with (s := 1 + (n - 1)) by omega.
    rewrite Zrange_empty with (n := 1 - 1) by omega.
    unfold prod_list at 3; ring.
  + apply Z.ltb_ge in e.
    now rewrite Zrange_empty by omega.
Qed.

Fixpoint Ztake_every_n {A : Type} (l : list A) (n o : Z) : list A :=
  match l with 
    | h :: t => 
        if o mod n =? 0 then
          h :: (Ztake_every_n t n (o + 1))
        else
          Ztake_every_n t n (o + 1)
    | nil => nil
  end.

Lemma Ztake_every_n_nil {A : Type}:
  forall (n o : Z),
  Ztake_every_n (A := A) nil n o = nil.
Proof.
  now compute.
Qed.

Lemma Ztake_every_n_div {A : Type}:
  forall (h : A) (t : list A) (n o : Z),
  o mod n = 0 ->
  Ztake_every_n (h :: t) n o = h :: (Ztake_every_n t n (o + 1)).
Proof.
  intros h t n o n_div_o; simpl.
  rewrite n_div_o; now compute.
Qed.

Lemma Ztake_every_n_not_div {A : Type}:
  forall (h : A) (t : list A) (n o : Z),
  o mod n <> 0 ->
  Ztake_every_n (h :: t) n o = Ztake_every_n t n (o + 1).
Proof.
  intros h t n o n_not_div_o; simpl.
  assert (o mod n =? 0 = false) as Hrw by now apply Z.eqb_neq. 
  now rewrite Hrw.
Qed.

Lemma Ztake_every_n_only_mod_matters {A : Type}:
  forall (l : list A) (n o : Z),
  0 < n ->
  Ztake_every_n l n o = Ztake_every_n l n (o mod n).
Proof.
  induction l as [|h t]; intros n o n_gt_0.
  + now compute.
  + assert ((o mod n) mod n = o mod n) as mod_mod by now rewrite Z.mod_mod by omega.
    assert ((o + 1) mod n = (o mod n + 1) mod n) as mod_rw.
    {
      destruct (Z_eq_dec n 1) as [n_eq_1 | n_ne_1].
      + subst; now repeat rewrite Z.mod_1_r.
      + now rewrite Z.add_mod, Z.mod_small with (a := 1) by omega.
    }
    cut (Ztake_every_n t n (o + 1) = Ztake_every_n t n (o mod n + 1)).
    - destruct (Z_eq_dec (o mod n) 0) as [n_div_o | n_not_div_o].
      * repeat rewrite Ztake_every_n_div by omega; intros H; now apply f_equal.
      * now repeat rewrite Ztake_every_n_not_div by omega.
    - rewrite IHt with (o := o + 1) by omega.
      rewrite IHt with (o := o mod n + 1) by omega.
      now rewrite mod_rw.
Qed.

Lemma Ztake_every_n_app {A : Type}:
  forall (l l' : list A) (n o : Z),
  Ztake_every_n (l ++ l') n o = 
  (Ztake_every_n l n o) ++ (Ztake_every_n l' n (o + Zlength l)).
Proof.
  induction l as [|h t]; intros l' n o.
  + rewrite Ztake_every_n_nil, Zlength_nil; repeat rewrite app_nil_l.
    now rewrite Z.add_0_r.
  + destruct (Z_eq_dec (o mod n) 0) as [n_div_o | n_not_div_o].
    - rewrite <-app_comm_cons; repeat rewrite Ztake_every_n_div by omega.
      rewrite <-app_comm_cons, Zlength_cons; apply f_equal.
      assert (o + Z.succ (Zlength t) = (o + 1) + Zlength t) as Hrw by omega;
        rewrite Hrw; clear Hrw.
      apply IHt.
    - rewrite <-app_comm_cons; repeat rewrite Ztake_every_n_not_div by omega.
      rewrite Zlength_cons.
      assert (o + Z.succ (Zlength t) = (o + 1) + Zlength t) as Hrw by omega;
        rewrite Hrw; clear Hrw.
      apply IHt.
Qed.

Lemma Ztake_every_n_skip_all {A : Type}:
  forall (l : list A) (n o : Z),
  0 < o ->
  Zlength l <= n - o ->
  Ztake_every_n l n o = nil.
Proof.
  induction l as [|h t]; intros n o o_gt_0 len_bound.
  + now compute.
  + rewrite Zlength_cons in len_bound.
    rewrite Ztake_every_n_not_div.
    - now rewrite IHt by omega.
    - assert (o mod n = o) as Hrw.
      {
        rewrite Z.mod_small; try split; try omega.
        assert (0 <= Zlength t) as len_lower_bound by apply Zlength_ge_0.
        omega.
      }
      rewrite Hrw; omega.
Qed.

Lemma div_aux_0:
  forall (n k : Z),
  0 < k ->
  n <= 0 <->
  (n - 1) / k + 1 <= 0.
Proof.
  intros n k k_gt_0; split.
  + intros n_le_0; cut ((n - 1) / k <= -1); try omega.
    cut ((n - 1) / k < 0); try omega.
    apply Z.div_lt_upper_bound; try rewrite Z.mul_0_r; omega.
  + destruct (Z_le_dec n 0) as [n_le_0 | n_gt_0]; auto.
    assert (0 <= (n - 1) / k) as Habs
      by (apply Z.div_pos; omega).
    omega.
Qed.

Lemma div_aux_1:
  forall (n k : Z),
  0 < k ->
  n <= k <->
  (n - 1) / k + 1 <= 1.
Proof.
  intros n k k_gt_0.
  assert ((n - k) <= 0 <-> n <= k) as Hrw by omega.
  rewrite <-Hrw; clear Hrw.
  assert (n - 1 = (n - k) - 1 + 1 * k) as Hrw by ring.
  rewrite Hrw; clear Hrw.
  rewrite Z.div_add by omega.
  assert ((n - k - 1) / k + 1 + 1 <= 1 <-> (n - k - 1) / k + 1 <= 0) as Hrw by omega.
  rewrite Hrw; clear Hrw.
  now apply div_aux_0.
Qed.

Lemma div_aux_2:
  forall (n k : Z),
  k <> 0 ->
  (n - k - 1) / k + 1 = (n - 1) / k.
Proof.
  intros n k k_ne_0.
  assert (n - k - 1 = (n - 1) + (-1)*k) as Hrw by ring; rewrite Hrw; clear Hrw.
  rewrite Z.div_add; omega.
Qed.

Lemma Zrange_take_every_n_is_stride {A : Type}:
  forall (s n k : Z),
  0 < k ->
  Ztake_every_n (Zrange s n) k 0 = Zrange_stride s ((n - 1) / k + 1) k.
Proof.
  intros s n k k_gt_0.
  destruct (Z_le_dec n 0) as [n_le_0 | n_gt_0].
  + rewrite Zrange_empty by omega.
    rewrite Zrange_stride_empty by (apply div_aux_0; omega).
    now compute.
  + revert s; generalize n_gt_0; apply Zlt_0_ind with (x := n); try omega.
    clear n n_gt_0; intros n Hind _ n_gt_0 s.
    assert (0 < (n - 1) / k + 1) as n_lo_bound.
    {
      cut (~((n - 1) / k + 1 <= 0)); try omega.
      intro Habs; now apply div_aux_0 in Habs.
    }
    rewrite Zrange_stride_cons by omega.
    destruct (Z_le_dec n k) as [n_le_k | n_gt_k].
    - assert (n = 1 + (n - 1)) as Hrw by omega; rewrite Hrw at 1; clear Hrw.
      rewrite Zrange_app, Ztake_every_n_app by omega.
      assert ((n - 1) / k + 1 - 1 = 0) as Hrw.
      {
        assert ((n - 1) / k + 1 <= 1) as n_hi_bound
          by (rewrite <-div_aux_1; omega).
        omega.
      }
      rewrite Hrw at 1; clear Hrw.
      rewrite Zrange_stride_empty, Zrange_length, Zrange_cons, Zrange_empty
        by omega.
      rewrite Ztake_every_n_skip_all with (o := 0 + 1); try omega.
      * now compute.
      * rewrite Zrange_length; omega.
    - assert (n = 1 + ((k - 1) + (n - k))) as Hrw by omega.
      rewrite Hrw at 1; clear Hrw.
      repeat rewrite Zrange_app by omega; repeat rewrite Ztake_every_n_app by omega.
      repeat rewrite Zrange_length by omega.
      rewrite Ztake_every_n_only_mod_matters with (o := 0 + 1 + (k - 1)) by omega.
      assert (0 + 1 + (k - 1) = k) as Hrw by omega; rewrite Hrw; clear Hrw.
      rewrite Z.mod_same, Hind with (y := n - k) by omega.
      rewrite Ztake_every_n_skip_all with (o := 0 + 1).
      * simpl Ztake_every_n at 1.
        assert (s + 1 + (k - 1) = s + k) as Hrw by omega; rewrite Hrw; clear Hrw.
        assert ((n - k - 1) / k + 1 = (n - 1) / k + 1 - 1) as Hrw
          by (rewrite div_aux_2; omega); rewrite Hrw; clear Hrw.
        now simpl.
      * omega.
      * rewrite Zrange_length; omega.
Qed.

Definition div_list_by_scalar (l : list Z) (d : Z) : list Z :=
  map (fun (x : Z) => x / d) l.

Lemma Zrange_stride_div:
  forall (s n k : Z),
  0 < k ->
  div_list_by_scalar (Zrange_stride s n k) k = Zrange (s / k) n.
Proof.
  intros s n k k_gt_0; revert s.
  destruct (Z_le_dec 0 n) as [n_ge_0 | n_lt_0].
  + apply Zlt_0_ind with (x := n); auto; clear n n_ge_0.
    intros n Hind n_ge_0 s.
    destruct (Z_eq_dec 0 n) as [n_eq_0 | n_ne_0].
    - subst; rewrite Zrange_empty, Zrange_stride_empty by omega.
      now compute.
    - rewrite Zrange_stride_cons, Zrange_cons by omega.
      simpl; rewrite Hind by omega.
      rewrite <-Z.mul_1_l with (n := k) at 2.
      now rewrite Z.div_add by omega.
  + intros s; rewrite Zrange_empty, Zrange_stride_empty by omega.
    now compute.
Qed.

Lemma Zrange_filter_mod_is_take_every_n:
  forall (s n k m : Z),
  0 < k ->
  filter (fun (x : Z) => x mod k =? m mod k) (Zrange s n) =
  Ztake_every_n (Zrange s n) k ((s - m) mod k).
Proof.
  intros s n k m k_gt_0; revert s m.
  destruct (Z_le_dec 0 n) as [n_ge_0 | n_lt_0].
  + apply Zlt_0_ind with (x := n); auto; clear n n_ge_0.
    intros n Hind n_ge_0 s m.
    destruct (Z_eq_dec n 0) as [n_eq_0 | n_ne_0].
    - subst; rewrite Zrange_empty by omega; now compute.
    - rewrite Zrange_cons by omega; simpl.
      destruct (Z_eq_dec (s mod k) (m mod k)) as [s_eqmod_m | s_neqmod_m].
      * assert (s mod k =? m mod k = true) as Hrw by now apply Z.eqb_eq.
        rewrite Hrw; clear Hrw.
        assert (((s - m) mod k) mod k =? 0 = true) as Hrw.
        {
          rewrite Zminus_mod, s_eqmod_m.
          assert (m mod k - m mod k = 0) as Hrw by omega; rewrite Hrw; clear Hrw.
          now compute.
        }
        rewrite Hrw; clear Hrw.
        rewrite Hind by omega.
        rewrite Ztake_every_n_only_mod_matters with (o := (s - m) mod k + 1) by omega.
        assert ((s + 1 - m) mod k = ((s - m) mod k + 1) mod k) as Hrw.
        {
          assert (s + 1 - m = s - m + 1) as Hrw by omega; rewrite Hrw; clear Hrw.
          rewrite Z.add_mod_idemp_l; omega.
        }
        now rewrite Hrw.
      * assert (s mod k =? m mod k = false) as Hrw by now apply Z.eqb_neq.
        rewrite Hrw; clear Hrw.
        assert (((s - m) mod k) mod k =? 0 = false) as Hrw.
        {
          apply Z.eqb_neq; rewrite Z.mod_mod, Zminus_mod by omega.
          assert (0 <= s mod k < k) as s_mod_bound by now apply Z.mod_pos_bound.
          assert (0 <= m mod k < k) as m_mod_bound by now apply Z.mod_pos_bound.
          destruct (Z_le_dec (m mod k) (s mod k)) as [m_le_s_mod | m_gt_s_mod].
          + rewrite Z.mod_small; omega.
          + rewrite <-Z.mod_add with (b := 1), Z.mul_1_l by omega.
            rewrite Z.mod_small; omega.
        }
        rewrite Hrw; clear Hrw.
        rewrite Hind by omega.
        rewrite Ztake_every_n_only_mod_matters with (o := (s - m) mod k + 1) by omega.
        assert ((s + 1 - m) mod k = ((s - m) mod k + 1) mod k) as Hrw.
        {
          assert (s + 1 - m = s - m + 1) as Hrw by omega; rewrite Hrw; clear Hrw.
          rewrite Z.add_mod_idemp_l; omega.
        }
        now rewrite Hrw.
  + intros s m; rewrite Zrange_empty by omega; now compute.
Qed.

Function Zfactor_exp (a f : Z) {measure Z.abs_nat a} : Z :=
  if ((1 <? f) && (0 <? a) && (a mod f =? 0)) then
    1 + Zfactor_exp (a / f) f
  else
    0.
Proof.
  intros a f rec_cond.
  repeat rewrite andb_true_iff in rec_cond.
  destruct rec_cond as [[f_gt_1 a_gt_0] f_div_a].
  apply Z.ltb_lt in f_gt_1; apply Z.ltb_lt in a_gt_0; apply Z.eqb_eq in f_div_a.
  apply Zabs2Nat.inj_lt; try omega.
  + apply Z.div_pos; omega.
  + apply Z.div_lt; omega.
Defined.

Lemma Zfactor_exp_ge_0:
  forall (a f : Z),
  0 <= Zfactor_exp a f.
Proof.
  intros a f; functional induction (Zfactor_exp a f); omega.
Qed.

Lemma Zfactor_exp_a_le_0:
  forall (a f : Z),
  a <= 0 ->
  Zfactor_exp a f = 0.
Proof.
  intros a f a_le_0; functional induction (Zfactor_exp a f); auto.
  repeat rewrite andb_true_iff in e.
  repeat rewrite Z.ltb_lt in e; omega.
Qed.

Lemma Zfactor_exp_f_le_1:
  forall (a f : Z),
  f <= 1 ->
  Zfactor_exp a f = 0.
Proof.
  intros a f f_le_1; functional induction (Zfactor_exp a f).
  + repeat rewrite andb_true_iff in e; destruct e as [[f_gt_1 _] _].
    apply Z.ltb_lt in f_gt_1; omega.
  + auto.
Qed.

Lemma Zfactor_exp_not_div:
  forall (a f e : Z),
  1 < f ->
  0 < a ->
  Zfactor_exp a f = 0 <->
  ~(f | a).
Proof.
  intros a f e f_gt_1 a_gt_0; functional induction (Zfactor_exp a f).
  + repeat rewrite andb_true_iff in e0; destruct e0 as [_ Habs].
    apply Z.eqb_eq in Habs; split.
    - intros Habs'.
      assert (0 <= Zfactor_exp (a / f) f) as rec_ge_0 by apply Zfactor_exp_ge_0.
      omega.
    - apply Zmod_divide in Habs; try omega; tauto.
  + repeat rewrite andb_false_iff in e0; repeat rewrite Z.ltb_ge in e0.
    rewrite Z.eqb_neq in e0; destruct e0 as [[Habs | Habs] | f_not_div_a]; try omega.
    split; auto; intros _.
    intro Habs; apply f_not_div_a.
    now apply Zdivide_mod.
Qed.

Lemma Zfactor_exp_div:
  forall (a f: Z),
  1 < f ->
  0 < a ->
  Zfactor_exp a f = 1 + Zfactor_exp (a / f) f <->
  (f | a).
Proof.
  intros a f f_gt_1 a_gt_0; functional induction (Zfactor_exp a f).
  + split; auto; intros _.
    repeat rewrite andb_true_iff in e; destruct e as [[_ _] f_div_a].
    apply Z.eqb_eq in f_div_a.
    apply Z.mod_divide; omega.
  + assert (0 <= Zfactor_exp (a / f) f) as rec_ge_0 by apply Zfactor_exp_ge_0.
    split; try omega; intros [k Habs].
    repeat rewrite andb_false_iff in e; repeat rewrite Z.ltb_ge in e.
    rewrite Z.eqb_neq in e; destruct e as [[Habs' | Habs'] | f_not_div_a]; try omega.
    subst; rewrite Z.mod_mul in f_not_div_a; omega.
Qed.

Lemma Zfactor_exp_1_is_0:
  forall (f : Z),
  Zfactor_exp 1 f = 0.
Proof.
  intros f; destruct (Z_le_dec f 1) as [f_le_1 | f_gt_1].
  + now rewrite Zfactor_exp_f_le_1.
  + apply Zfactor_exp_not_div; auto; try omega.
    intros Habs; apply Z.divide_1_r_nonneg in Habs; omega.
Qed.

Lemma Zfactor_exp_works:
  forall (a f e : Z),
  1 < f ->
  0 < a ->
  e = Zfactor_exp a f <->
  (f^e | a) /\ ~(f^(e + 1) | a).
Proof.
  intros a f e f_gt_1 a_gt_0; revert f e f_gt_1; generalize a_gt_0.
  apply Zlt_0_ind with (x := a); try omega; clear a a_gt_0.
  intros a Hind _ a_gt_0 f e f_gt_1.
  destruct (Zdivide_dec f a) as [f_div_a | f_not_div_a].
  + assert (Zfactor_exp a f = 1 + Zfactor_exp (a / f) f) as Hrw
      by now apply Zfactor_exp_div.
    rewrite Hrw; clear Hrw.
    remember (e - 1) as e'; assert (e = e' + 1) as Hrw by omega.
    rewrite Hrw; clear Hrw.
    assert (e' = Zfactor_exp (a / f) f <-> e' + 1 = 1 + Zfactor_exp (a / f) f) as Hrw
      by omega; rewrite <-Hrw; clear Hrw.
    destruct f_div_a as [a' f_div_a].
    destruct (Z_le_dec 0 e') as [e'_ge_0 | e'_lt_0].
    - rewrite f_div_a.
      do 2 rewrite Z.pow_add_r, Z.pow_1_r by omega.
      repeat rewrite Z.mul_divide_cancel_r by omega.
      rewrite Z.div_mul by omega.
      assert (0 < a') as a'_gt_0.
      {
        rewrite f_div_a in a_gt_0.
        apply Zmult_lt_0_reg_r with (n := f); omega.
      }
      assert (a' < a) as a'_lt_a.
      {
        rewrite f_div_a, <-Z.mul_1_r at 1.
        apply Z.mul_lt_mono_pos_l; omega.
      }
      apply Hind; omega.
    - assert (0 <= Zfactor_exp (a / f) f) as rec_ge_0 by apply Zfactor_exp_ge_0.
      split; try omega.
      intros [Habs Habs'].
      destruct (Z_lt_dec e' (-1)) as [e'_lt_m1 | e'_ge_m1].
      * rewrite Z.pow_neg_r in Habs by omega.
        apply Z.divide_0_l in Habs; omega.
      * assert (e' = -1) as Hrw by omega; rewrite Hrw in *; clear Hrw.
        assert (-1 + 1 + 1 = 1) as Hrw by omega; rewrite Hrw in Habs'; clear Hrw.
        exfalso; apply Habs'; rewrite Z.pow_1_r.
        now exists a'.
  + assert (Zfactor_exp a f = 0) as Hrw by now apply Zfactor_exp_not_div.
    rewrite Hrw; clear Hrw; split.
    - intros e_eq_0; subst; rewrite Z.pow_0_r, Z.add_0_l, Z.pow_1_r; split; auto.
      apply Z.divide_1_l.
    - destruct (Z.lt_trichotomy 0 e) as [e_gt_e | [e_eq_0 | e_lt_0]].
      * intros [[k Habs] _]; assert (e = 1 + (e - 1)) as Hrw by omega;
          rewrite Hrw in Habs; clear Hrw.
        rewrite Z.pow_add_r in Habs by omega.
        exfalso; apply f_not_div_a.
        exists (k * f^(e - 1)); rewrite Habs; ring.
      * auto.
      * intros [Habs _]; rewrite Z.pow_neg_r in Habs by omega.
        apply Z.divide_0_l in Habs; omega.
Qed.

Fixpoint pos_list (l : list Z) : Prop :=
  match l with
    | h :: t => 0 < h /\ pos_list t
    | nil => True
  end.

Lemma prod_pos_list_is_pos:
  forall (l : list Z),
  pos_list l ->
  0 < prod_list l.
Proof.
  induction l as [|h t].
  + now compute.
  + intros [h_gt_0 t_is_pos]; simpl.
    specialize (IHt t_is_pos).
    apply Z.mul_pos_pos; omega.
Qed.

Lemma not_div_prod:
  forall (a b d : Z),
  ~(d | a * b) ->
  ~(d | a) /\ ~(d | b).
Proof.
  intros a b d not_d_div_ab; split.
  + intros [a' d_div_a_abs]; apply not_d_div_ab; exists (a' * b); subst; ring.
  + intros [b' d_div_b_abs]; apply not_d_div_ab; exists (a * b'); subst; ring.
Qed.

Lemma Zfactor_exp_prod_factor:
  forall (a f : Z),
  0 < a ->
  1 < f ->
  Zfactor_exp (a * f) f = 1 + Zfactor_exp a f.
Proof.
  intros a f a_gt_0 f_gt_1.
  cut (Zfactor_exp (a * f) f = 1 + Zfactor_exp (a * f / f) f).
  + now rewrite Z.div_mul by omega.
  + apply Zfactor_exp_div.
    - omega.
    - apply Z.mul_pos_pos; omega.
    - now exists a.
Qed.

Lemma Zfactor_exp_prod_prime:
  forall (a b f : Z),
  0 < a ->
  0 < b ->
  prime f ->
  Zfactor_exp a f + Zfactor_exp b f = Zfactor_exp (a * b) f.
Proof.
  intros a b f a_gt_0 b_gt_0 f_is_prime.
  assert (2 <= f) as f_ge_2 by now apply prime_ge_2.
  assert (0 < a * b) as ab_gt_0 by now apply Z.mul_pos_pos.
  remember (a * b) as ab eqn:ab_def.
  revert a b a_gt_0 b_gt_0 ab_def; generalize ab_gt_0.
  apply Zlt_0_ind with (x := ab); try omega; clear ab ab_gt_0.
  intros ab Hind _ ab_gt_0 a b a_gt_0 b_gt_0 ab_def.
  destruct (Zdivide_dec f ab) as [f_div_ab | not_f_div_ab]; subst.
  + apply prime_mult in f_div_ab as f_div_a_or_b; auto.
    destruct f_div_ab as [ab' f_div_ab].
    assert (0 < ab') as ab'_gt_0 by (apply Zmult_lt_0_reg_r with (n := f); omega).
    assert (ab' < a * b) as ab'_lt_ab
      by (rewrite f_div_ab, <-Z.mul_1_r at 1; apply Z.mul_lt_mono_pos_l; omega).
    rewrite f_div_ab, Zfactor_exp_prod_factor by omega.
    destruct f_div_a_or_b as [[a' f_div_a'] | [b' f_div_b']].
    - assert (0 < a') as a'_gt_0 by (apply Zmult_lt_0_reg_r with (n := f); omega).
      rewrite f_div_a', Zfactor_exp_prod_factor by omega.
      rewrite <-Z.add_assoc, Hind with (a := a') (b := b) (y := ab'); try omega.
      apply Z.mul_reg_r with (p := f); try omega.
      rewrite <-f_div_ab, f_div_a'; ring.
    - assert (0 < b') as b'_gt_0 by (apply Zmult_lt_0_reg_r with (n := f); omega).
      rewrite f_div_b', Zfactor_exp_prod_factor by omega.
      rewrite Z.add_comm, <-Z.add_assoc, Hind with (a := b') (b := a) (y := ab'); try omega.
      apply Z.mul_reg_r with (p := f); try omega.
      rewrite <-f_div_ab, f_div_b'; ring.
  + apply not_div_prod in not_f_div_ab as not_f_div_a_and_b.
    destruct not_f_div_a_and_b as [not_f_div_a not_f_div_b].
    assert (forall (x : Z), 0 < x -> ~(f | x) -> Zfactor_exp x f = 0) as Hrw
      by (intros x not_f_div_x; apply Zfactor_exp_not_div; auto; omega).
    now repeat rewrite Hrw by auto.
Qed.

Lemma Zfactor_exp_prod_list_prime:
  forall (l : list Z) (f : Z),
  pos_list l ->
  prime f ->
  sum_list (map (fun (x : Z) => Zfactor_exp x f) l) = 
  Zfactor_exp (prod_list l) f.
Proof.
  induction l as [|h t].
  + intros f _ f_is_prime.
    simpl sum_list; simpl prod_list.
    now rewrite Zfactor_exp_1_is_0.
  + intros f [h_gt_0 t_is_pos] f_is_prime; simpl.
    assert (0 < prod_list t) as prod_t_gt_0 by now apply prod_pos_list_is_pos.
    rewrite <-Zfactor_exp_prod_prime by auto.
    now rewrite IHt by auto.
Qed.

Lemma Zrange_stride_start_pos_is_pos:
  forall (s n k : Z),
  0 < s ->
  0 < k ->
  pos_list (Zrange_stride s n k).
Proof.
  intros s n; revert s.
  destruct (Z_le_dec 0 n) as [n_ge_0 | n_lt_0].
  + apply Zlt_0_ind with (x := n); auto; clear n n_ge_0.
    intros n Hind n_ge_0 s k s_gt_0 k_gt_0.
    destruct (Z_eq_dec n 0) as [n_eq_0 | n_ne_0].
    - subst; now rewrite Zrange_stride_empty by omega.
    - rewrite Zrange_stride_cons by omega; simpl; split.
      * auto.
      * apply Hind; omega.
  + intros s k _ _; now rewrite Zrange_stride_empty by omega.
Qed.

Lemma Zrange_start_pos_is_pos:
  forall (s n : Z),
  0 < s ->
  pos_list (Zrange s n).
Proof.
  intros s n s_gt_0; unfold Zrange.
  apply Zrange_stride_start_pos_is_pos; omega.
Qed.

Lemma sum_list_equiv_filter:
  forall (f : Z -> bool) (l : list Z),
  (forall (x : Z), f x = false -> x = 0) ->
  sum_list l = sum_list (filter f l).
Proof.
  intros f l Hfilter; induction l as [|h t].
  + now compute.
  + simpl; remember (f h) as f_h.
    destruct f_h as [f_h_true | f_h_false].
    - simpl; now rewrite IHt.
    - rewrite Hfilter with (x := h) by auto.
      now rewrite IHt.
Qed.

Lemma filter_map_comm {A B : Type}:
  forall (f1 : B -> bool) (f2 : A -> bool) (g : A -> B) (l : list A),
  (forall (a : A), f1 (g a) = f2 a) ->
  filter f1 (map g l) = map g (filter f2 l).
Proof.
  intros f1 f2 g l Hfilter_comm; induction l as [|h t].
  + now compute.
  + simpl; remember (f2 h) as f2_h; destruct f2_h as [f2_h_true | f2_h_false];
      now rewrite Hfilter_comm, <-Heqf2_h, IHt.
Qed.

Lemma filter_equiv_pos:
  forall (f1 f2 : Z -> bool) (l : list Z),
  pos_list l ->
  (forall (x : Z), 0 < x -> f1 x = f2 x) ->
  filter f1 l = filter f2 l.
Proof.
  intros f1 f2 l l_is_pos f_equiv; induction l as [|h t].
  + now compute.
  + simpl; destruct l_is_pos as [h_gt_0 t_is_pos].
    now rewrite f_equiv, IHt by (auto; omega).
Qed.

Lemma Zrange_stride_is_mul_by_scalar:
  forall (s n k : Z),
  0 < k ->
  Zrange_stride s n k = 
  map (fun (x : Z) => s mod k + k * x) (Zrange (s / k) n).
Proof.
  intros s n k k_gt_0; revert s.
  destruct (Z_le_dec 0 n) as [n_ge_0 | n_lt_0].
  + apply Zlt_0_ind with (x := n); auto; clear n n_ge_0.
    intros n Hind n_ge_0 s.
    destruct (Z_eq_dec n 0) as [n_eq_0 | n_ne_0].
    - subst; now rewrite Zrange_stride_empty, Zrange_empty.
    - rewrite Zrange_cons, Zrange_stride_cons by omega.
      rewrite Hind by omega; simpl map.
      apply f_equal2.
      * now rewrite Z.add_comm, <-Z.div_mod by omega.
      * assert ((s + k) mod k = s mod k) as Hrw.
        {
          rewrite <-Z.mul_1_l with (n := k) at 1.
          rewrite Z.mod_add; omega.
        }
        rewrite Hrw; clear Hrw.
        assert ((s + k) / k = s / k + 1) as Hrw.
        {
          rewrite <-Z.mul_1_l with (n := k) at 1.
          now rewrite Z.div_add by omega.
        }
        now rewrite Hrw.
  + intros s; now rewrite Zrange_stride_empty, Zrange_empty by omega.
Qed.

Lemma sum_list_add_map {A : Type}:
  forall (f g : A -> Z) (l : list A) (o : Z),
  (forall (a : A), f a = o + g a) ->
  sum_list (map f l) = o * (Zlength l) + sum_list (map g l).
Proof.
  intros f g l o Heq; induction l as [|h t].
  + rewrite Zlength_nil; simpl; ring.
  + rewrite Zlength_cons; simpl; rewrite IHt, Z.mul_succ_r, Heq.
    ring.
Qed.

Lemma map_ext_pos_list:
  forall (f g : Z -> Z) (l : list Z),
  pos_list l ->
  (forall (a : Z), 0 < a -> f a = g a) ->
  map f l = map g l.
Proof.
  intros f g l l_is_pos Heq.
  induction l as [|h t].
  + now compute.
  + simpl in *.
    now rewrite Heq, IHt by tauto.
Qed.

Theorem Zfactor_exp_fact_rec:
  forall (n p : Z),
  0 < n ->
  prime p ->
  Zfactor_exp (Zfact n) p = 
  n / p + (Zfactor_exp (Zfact (n / p)) p).
Proof.
  intros n p n_gt_0 p_is_prime.
  assert (2 <= p) as p_ge_2 by now apply prime_ge_2.
  repeat rewrite Zfact_is_prod_list.
  repeat rewrite <-Zfactor_exp_prod_list_prime
    by (auto; now apply Zrange_start_pos_is_pos).
  assert (forall x : Z, negb (x =? 0) = false -> x = 0) as outer_filter
    by (intros x; now rewrite negb_false_iff, Z.eqb_eq).
  rewrite sum_list_equiv_filter with (f := fun (x : Z) => negb (x =? 0)) by auto.
  remember (fun x : Z => negb (x =? 0)) as f1.
  remember (fun x : Z => Zfactor_exp x p) as g.
  remember (fun x : Z => (x mod p =? 0) && (0 <? x)) as f2.
  remember (fun x : Z => x mod p =? 0 mod p) as f3.
  assert (forall (x : Z), f1 (g x) = f2 x) as filter_comm.
  {
    intros x; subst; apply eq_iff_eq_true.
    rewrite negb_true_iff, andb_true_iff, Z.eqb_eq, Z.eqb_neq, Z.ltb_lt.
    assert (x mod p = 0 <-> (p | x)) as Hrw
      by (split; try apply Zmod_divide; try apply Zdivide_mod; omega).
    rewrite Hrw.
    cut (Zfactor_exp x p = 0 <-> ~(p | x) \/ ~(0 < x)).
    + destruct (Z_eq_dec (Zfactor_exp x p) 0),
               (Z_eq_dec (x mod p) 0),
               (Z_lt_dec 0 x); tauto.
    + destruct (Z_lt_dec 0 x) as [x_gt_0 | x_le_0].
      - assert (~(p | x) \/ ~(0 < x) <-> ~(p | x)) as Hrw' by tauto.
        rewrite Hrw'.
        apply Zfactor_exp_not_div; auto; omega.
      - rewrite Zfactor_exp_a_le_0 by omega; tauto.
  }
  rewrite filter_map_comm with (f5 := f2); auto.
  assert (pos_list (Zrange 1 n)) as range_is_pos by now apply Zrange_start_pos_is_pos.
  assert (forall (x : Z), 0 < x -> f2 x = f3 x) as f2_equiv_f3.
  {
    intros x x_gt_0; subst.
    assert (0 <? x = true) as Hrw by now apply Z.ltb_lt. rewrite Hrw; clear Hrw.
    now rewrite andb_true_r.
  }
  rewrite filter_equiv_pos with (f2 := f3) by auto.
  subst f3; rewrite Zrange_filter_mod_is_take_every_n by omega.
  destruct (Z_lt_dec n p) as [n_lt_p | n_ge_p].
  + assert (n / p = 0) as Hrw by (apply Z.div_small; omega); repeat rewrite Hrw; clear Hrw.
    rewrite Zrange_empty with (n := 0) by omega.
    rewrite Ztake_every_n_skip_all.
    - now compute.
    - rewrite Z.mod_small; omega.
    - rewrite Zrange_length, Z.mod_small; omega.
  + assert (n = (p - 1) + (n - p + 1)) as Hrw by omega; rewrite Hrw at 1; clear Hrw.
    rewrite Zrange_app, Ztake_every_n_app by omega.
    assert ((1 - 0) mod p = 1) as Hrw by (rewrite Z.mod_small; omega); rewrite Hrw; clear Hrw.
    rewrite Zrange_length by omega.
    assert (Zlength (Zrange 1 (p - 1)) = p - 1) as Haux by (apply Zrange_length; omega).
    rewrite Ztake_every_n_skip_all, app_nil_l by omega.
    assert (1 + (p - 1) = p) as Hrw by omega; rewrite Hrw; clear Hrw Haux.
    rewrite Ztake_every_n_only_mod_matters, Z.mod_same by omega.
    rewrite (Zrange_take_every_n_is_stride (A := Z)) by omega.
    rewrite Zrange_stride_is_mul_by_scalar by omega.
    remember (fun (x : Z) => 1 + Zfactor_exp x p) as g2.
    assert (forall (a : Z), 0 < a -> g (p mod p + p * a) = g2 a) as Haux.
    {
      subst; intros a a_gt_0; rewrite Z.mod_same, Z.add_0_l by omega.
      now rewrite Z.mul_comm, Zfactor_exp_prod_factor by omega.
    }
    assert (pos_list (Zrange (p / p) ((n - p + 1 - 1) / p + 1))) as Haux'
      by (apply Zrange_start_pos_is_pos; rewrite Z.div_same; omega).
    rewrite map_map, map_ext_pos_list with (g := g2) by auto; clear Haux.
    rewrite Z.div_same by omega.
    assert ((n - p + 1 - 1) / p + 1 = n / p) as Hrw.
    {
      assert (n - p + 1 - 1 = n + (-1) * p) as Hrw by ring; rewrite Hrw; clear Hrw.
      rewrite Z.div_add; omega.
    }
    rewrite Hrw; clear Hrw.
    assert (forall (a : Z), g2 a = 1 + g a) as Haux by now subst.
    rewrite sum_list_add_map with (f := g2) (g0 := g) (o := 1) by auto; clear Haux.
    assert (0 < n / p) as n_over_p_gt_0 by (apply Z.div_str_pos; omega).
    rewrite Zrange_length by omega.
    ring.
Qed.

Function Zprime_factor_exp_fact (n p : Z) {measure Zabs_nat n} : Z :=
  if (0 <? n) && (1 <? p) then
    n / p + (Zprime_factor_exp_fact (n / p) p)
  else
    0.
Proof.
  intros n p bool_cond.
  rewrite andb_true_iff in bool_cond.
  repeat rewrite Z.ltb_lt in bool_cond.
  apply Zabs2Nat.inj_lt; try omega.
  + apply Z.div_pos; omega.
  + apply Z.div_lt; omega.
Defined.

Lemma Zprime_factor_exp_fact_base:
  forall (n p : Z),
  (n <= 0) \/ (p <= 1) ->
  Zprime_factor_exp_fact n p = 0.
Proof.
  intros n p Hcond; functional induction (Zprime_factor_exp_fact n p).
  + rewrite andb_true_iff in e; repeat rewrite Z.ltb_lt in e; omega.
  + auto.
Qed.

Lemma Zprime_factor_exp_fact_recursion:
  forall (n p : Z),
  (0 < n) /\ (1 < p) ->
  Zprime_factor_exp_fact n p =
  n / p + Zprime_factor_exp_fact (n / p) p.
Proof.
  intros n p Hcond; functional induction (Zprime_factor_exp_fact n p).
  + auto.
  + rewrite andb_false_iff in e; repeat rewrite Z.ltb_ge in e; omega.
Qed.

Lemma Zprime_factor_exp_fact_works:
  forall (n p : Z),
  0 <= n ->
  prime p ->
  Zfactor_exp (Zfact n) p = Zprime_factor_exp_fact n p.
Proof.
  intros n p n_ge_0; revert p. 
  apply Zlt_0_ind with (x := n); auto; clear n n_ge_0.
  intros n Hind n_ge_0 p p_is_prime.
  destruct (Z_eq_dec 0 n) as [n_eq_0 | n_ne_0].
  + subst; assert (Zfact 0 = 1) as Hrw by now compute. rewrite Hrw; clear Hrw.
    rewrite Zfactor_exp_1_is_0, Zprime_factor_exp_fact_base; omega.
  + rewrite Zfactor_exp_fact_rec by (auto; omega).
    assert (2 <= p) as p_ge_2 by now apply prime_ge_2.
    rewrite Zprime_factor_exp_fact_recursion by omega.
    rewrite Hind; auto.
    - split.
      * apply Z.div_pos; omega.
      * apply Z.div_lt; omega.
Qed.

Lemma Zprime_factor_exp_fact_ge_0:
  forall (n p : Z),
  0 <= Zprime_factor_exp_fact n p.
Proof.
  intros n p; functional induction (Zprime_factor_exp_fact n p).
  + rewrite andb_true_iff in e; repeat rewrite Z.ltb_lt in e.
    assert (0 <= n / p) as div_pos by (apply Z.div_pos; omega).
    omega.
  + omega.
Qed.

Lemma Zprime_factor_exp_fact_incr_in_n:
  forall (n n' p : Z),
  0 <= n <= n' ->
  1 < p ->
  Zprime_factor_exp_fact n p <= Zprime_factor_exp_fact n' p.
Proof.
  intros n n' p n_bound; assert (0 <= n') as n'_ge_0 by omega; revert n p n_bound.
  apply Zlt_0_ind with (x := n'); auto; clear n' n'_ge_0.
  intros n' Hind _ n p n_bound p_gt_1.
  destruct (Z_eq_dec n' 0) as [n'_eq_0 | n'_ne_0],
           (Z_eq_dec n 0) as [n_eq_0 | n_ne_0]; try omega.
  + repeat rewrite Zprime_factor_exp_fact_base; omega.
  + rewrite Zprime_factor_exp_fact_base by omega.
    apply Zprime_factor_exp_fact_ge_0.
  + rewrite Zprime_factor_exp_fact_recursion with (n := n) by omega.
    rewrite Zprime_factor_exp_fact_recursion with (n := n') by omega.
    assert (n / p <= n' / p) as div_le
      by (apply Z.div_le_mono; omega).
    assert (0 <= n / p) as div_nonneg
      by (apply Z.div_pos; omega).
    assert (n' / p < n') as div_upper_bound
      by (apply Z.div_lt; omega).
    assert (Zprime_factor_exp_fact (n / p) p <=
            Zprime_factor_exp_fact (n' / p) p) as rec_le
      by (apply Hind; omega).
    omega.
Qed.

Lemma Zprime_factor_exp_fact_decr_in_p:
  forall (n p p' : Z),
  0 <= n ->
  1 < p <= p' ->
  Zprime_factor_exp_fact n p' <= Zprime_factor_exp_fact n p.
Proof.
  intros n p p' n_ge_0; revert p p'.
  apply Zlt_0_ind with (x := n); auto; clear n n_ge_0.
  intros n Hind n_ge_0 p p' p_bounds.
  destruct (Z_eq_dec n 0) as [n_eq_0 | n_ne_0].
  + repeat rewrite Zprime_factor_exp_fact_base; omega.
  + rewrite Zprime_factor_exp_fact_recursion with (p := p) by omega.
    rewrite Zprime_factor_exp_fact_recursion with (p := p') by omega.
    assert (n / p' <= n / p) as div_le
      by (apply Z.div_le_compat_l; omega).
    assert (Zprime_factor_exp_fact (n / p) p' <=
            Zprime_factor_exp_fact (n / p) p) as rec_le.
    {
      apply Hind; try omega; split.
      + apply Z.div_pos; omega.
      + apply Z.div_lt; omega.
    }
    assert (Zprime_factor_exp_fact (n / p') p' <=
            Zprime_factor_exp_fact (n / p) p') as decr_n_le.
    {
      apply Zprime_factor_exp_fact_incr_in_n; try split; try omega.
      apply Z.div_pos; omega.
    }
    omega.
Qed.

Lemma mod_ne_0_not_div:
  forall (n d : Z),
  d <> 0 ->
  n mod d <> 0 ->
  ~(d | n).
Proof.
  intros n d d_ne_0 n_mod_d_ne_0.
  intros Habs; apply Z.mod_divide in Habs; omega.
Qed.

Lemma prime_5:
  prime 5.
Proof.
  rewrite <-prime_alt; unfold prime'.
  split; try omega.
  intros d d_bound.
  apply mod_ne_0_not_div; try omega.
  destruct (Z_eq_dec d 2), (Z_eq_dec d 3), (Z_eq_dec d 4); try omega; subst; now compute.
Qed.

Lemma div_10_to_2_5:
  forall (n a : Z),
  (10^a | n) ->
  (2^a | n) /\ (5^a | n).
Proof.
  intros n a [n' div_10]; split.
  + exists (n' * 5^a); subst; rewrite <-Z.mul_assoc, <-Z.pow_mul_l; now compute.
  + exists (n' * 2^a); subst; rewrite <-Z.mul_assoc, <-Z.pow_mul_l; now compute.
Qed.

Lemma prime_pow_not_div:
  forall (p q a : Z),
  prime p -> 
  prime q ->
  p <> q ->
  0 < a ->
  ~(q | p^a).
Proof.
  intros p q a p_is_prime q_is_prime p_ne_q a_gt_0.
  assert (0 <= a) as a_ge_0 by omega; revert a_gt_0.
  apply Zlt_0_ind with (x := a); auto; clear a a_ge_0.
  intros a Hind _ a_gt_0 Habs.
  assert (a = 1 + (a - 1)) as Hrw by omega; rewrite Hrw in Habs; clear Hrw.
  rewrite Z.pow_add_r, Z.pow_1_r in Habs by omega.
  destruct (Z_eq_dec a 1) as [a_eq_1 | a_ne_1].
  {
    subst; rewrite Z.pow_0_r, Z.mul_1_r in Habs.
    apply prime_div_prime in Habs; auto; omega.
  }
  cut ((q | p) \/ (q | p^(a - 1))).
  + intros [Habs' | Habs'].
    - apply prime_div_prime in Habs'; auto; omega.
    - apply Hind in Habs'; omega.
  + now apply prime_mult.
Qed.

Lemma div_prime_pow:
  forall (n p q a b : Z),
  prime p ->
  prime q ->
  p <> q ->
  (p^a | n) ->
  (q^b | n) ->
  (p^a * q^b | n).
Proof.
  intros n p q a b p_is_prime q_is_prime p_ne_q pow_p_div_n pow_q_div_n.
  destruct (Z_le_dec a 0) as [a_le_0 | a_gt_0].
  + destruct (Z_eq_dec a 0) as [a_eq_0 | a_ne_0].
    - destruct pow_q_div_n as [n' pow_q_div_n].
      exists n'; subst; rewrite Z.pow_0_r.
      ring.
    - rewrite Z.pow_neg_r in pow_p_div_n by omega; apply Z.divide_0_l in pow_p_div_n.
      exists 0; subst; ring.
  + destruct (Z_le_dec 0 b) as [b_ge_0 | b_lt_0].
    - revert pow_q_div_n.
      apply Zlt_0_ind with (x := b); auto; clear b b_ge_0.
      intros b Hind b_ge_0 pow_q_div_n.
      destruct (Z_eq_dec b 0) as [b_eq_0 | b_ne_0].
      * subst; now rewrite Z.pow_0_r, Z.mul_1_r.
      * destruct pow_q_div_n as [n'' pow_q_div_n].
        assert (exists (n' : Z), n = n' * (p^a * q^(b-1))) as [n' n'_def].
        {
          apply Hind; try omega.
          exists (n'' * q^1); rewrite <-Z.mul_assoc, <-Z.pow_add_r by omega.
          assert (1 + (b - 1) = b) as Hrw by omega; now rewrite Hrw.
        }
        rewrite pow_q_div_n in n'_def.
        assert (b = 1 + (b - 1)) as Hrw by omega; 
          rewrite Hrw in n'_def at 1; rewrite Hrw; clear Hrw.
        rewrite Z.pow_add_r in n'_def by omega; repeat rewrite Z.mul_assoc in n'_def.
        assert (q^(b - 1) <> 0) as Haux.
        {
          apply Z.pow_nonzero; try omega.
          cut (2 <= q); try omega.
          now apply prime_ge_2.
        }
        apply Z.mul_reg_r in n'_def; auto; clear Haux.
        rewrite Z.pow_1_r in n'_def.
        assert ((q | n')) as [m q_div_n'].
        {
          cut ((q | n') \/ (q | p^a)).
          + intros [H | Habs]; auto.
            apply prime_pow_not_div in Habs; auto; omega.
          + apply prime_mult; auto.
            now exists n''.
        }
        exists m; rewrite Z.pow_add_r, Z.pow_1_r by omega.
        assert (m * (p ^ a * (q * q ^ (b - 1))) =
                m * q * p^a * q^(b - 1)) as Hrw by ring.
        rewrite Hrw; clear Hrw.
        rewrite <-q_div_n', <-n'_def.
        rewrite <-Z.pow_1_r with (a := q) at 1.
        rewrite <-Z.mul_assoc, <-Z.pow_add_r by omega.
        assert (1 + (b - 1) = b) as Hrw by omega; now rewrite Hrw.
    - rewrite Z.pow_neg_r in pow_q_div_n by omega; apply Z.divide_0_l in pow_q_div_n.
      exists 0; subst; ring.
Qed.

Lemma div_2_5_to_10_aux:
  forall (n a b : Z),
  0 <= a ->
  0 <= b ->
  (2^a | n) ->
  (5^b | n) ->
  (10^(Z.min a b) | n).
Proof.
  intros n a b a_ge_0 b_ge_0 div_2 div_5; remember (Z.min a b) as c.
  assert (prime 2) as prime_2 by apply prime_2.
  assert (prime 5) as prime_5 by apply prime_5.
  assert ((2^a * 5^b | n)) as [n' div_prod]
    by (apply div_prime_pow; auto; omega).
  exists (n' * 2^(a - c) * 5^(b - c)); subst n.
  assert (10 = 2 * 5) as Hrw by now compute. rewrite Hrw; clear Hrw.
  assert (a = (a - c) + c) as Hrw by omega; rewrite Hrw at 1; clear Hrw.
  assert (b = (b - c) + c) as Hrw by omega; rewrite Hrw at 1; clear Hrw.
  assert (0 <= c) as c_ge_0
    by (subst; destruct (Zmin_irreducible a b); omega).
  assert (c <= a) as c_le_a
    by (subst; apply Z.le_min_l; auto).
  assert (c <= b) as c_le_b
    by (subst; apply Z.le_min_r; auto).
  repeat rewrite Z.pow_add_r; try omega.
  rewrite Z.pow_mul_l; ring.
Qed.

Lemma div_2_5_to_10:
  forall (n a b : Z),
  (2^a | n) ->
  (5^b | n) ->
  (10^(Z.min a b) | n).
Proof.
  intros n a b div_2 div_5.
  destruct (Z_lt_dec a 0) as [a_lt_0 | a_ge_0].
  + rewrite Z.pow_neg_r in div_2 by omega.
    apply Z.divide_0_l in div_2; subst.
    apply Z.divide_0_r.
  + destruct (Z_lt_dec b 0) as [b_lt_0 | b_ge_0].
    - rewrite Z.pow_neg_r in div_5 by omega.
      apply Z.divide_0_l in div_5; subst.
      apply Z.divide_0_r.
    - apply div_2_5_to_10_aux; auto; omega.
Qed.

Lemma Zfact_gt_0:
  forall (n : Z),
  0 <= n ->
  0 < Zfact n.
Proof.
  intros n n_ge_0; functional induction (Zfact n).
  + apply Z.ltb_lt in e; apply Z.mul_pos_pos; auto.
    apply IHz; omega.
  + omega.
Qed.

Lemma div_pow_le:
  forall (n a b b' : Z),
  0 <= b' <= b ->
  (a^b | n) ->
  (a^b' | n).
Proof.
  intros n a b b' b_bound [n' div_pow].
  exists (n' * a^(b - b')); subst.
  rewrite <-Z.mul_assoc, <-Z.pow_add_r by omega.
  assert (b - b' + b' = b) as Hrw by omega; now rewrite Hrw.
Qed.

Theorem main:
  forall (n d : Z),
  0 <= n ->
  d = Zprime_factor_exp_fact n 5 <->
  (10^d | Zfact n) /\ ~(10^(d+1) | Zfact n).
Proof.
  intros n d n_ge_0.
  pose prime_5; pose prime_2.
  assert (0 < Zfact n) as fact_gt_0 by now apply Zfact_gt_0.
  split.
  + intros d_def.
    assert (d <= Zprime_factor_exp_fact n 2) as d_bound
      by (subst; apply Zprime_factor_exp_fact_decr_in_p; omega).
    rewrite <-Zprime_factor_exp_fact_works in * by auto.
    remember (Zfactor_exp (Zfact n) 2) as d'.
    rewrite Zfactor_exp_works in * by omega.
    split.
    - assert (d = Z.min d' d) as Hrw
        by now apply eq_sym, Z.min_r.
      rewrite Hrw; clear Hrw.
      now apply div_2_5_to_10.
    - intros Habs; now apply div_10_to_2_5 in Habs.
  + intros [div_pow not_div_pow].
    apply div_10_to_2_5 in div_pow.
    rewrite <-Zprime_factor_exp_fact_works by auto.
    rewrite Zfactor_exp_works by omega.
    split; try tauto.
    intros Habs.
    remember (Zprime_factor_exp_fact n 5) as d'.
    remember (Zprime_factor_exp_fact n 2) as d''.
    assert (d' <= d'') as d'_d''_bound
      by (subst; apply Zprime_factor_exp_fact_decr_in_p; omega).
    rewrite <-Zprime_factor_exp_fact_works in * by auto.
    rewrite Zfactor_exp_works in * by omega.
    destruct (Z_lt_dec d 0) as [d_lt_0 | d_ge_0].
    {
      rewrite Z.pow_neg_r in div_pow by auto.
      destruct div_pow as [div_pow _]; apply Z.divide_0_l in div_pow; omega.
    }
    destruct (Z.lt_trichotomy d d') as [d_lt_d' | [d_eq_d' | d_gt_d']].
    - assert (2^(d+1) | Zfact n) as Habs'
        by (apply div_pow_le with (b := d''); try tauto; omega).
      assert (10^(d+1) | Zfact n) as Habs''.
      {
        assert (d + 1 = Z.min (d + 1) (d + 1)) as Hrw by now rewrite Z.min_l.
        rewrite Hrw; clear Hrw.
        now apply div_2_5_to_10.
      }
      tauto.
    - now subst.
    - destruct (Z_lt_dec d' 0) as [d'_lt_0 | d'_ge_0].
      {
        destruct Heqd' as [Heqd' _].
        rewrite Z.pow_neg_r in Heqd' by auto.
        apply Z.divide_0_l in Heqd'; omega.
      }
      now assert (5^(d'+1) | Zfact n) as Habs''
        by (apply div_pow_le with (b := d + 1); auto; omega).
Qed.