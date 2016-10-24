Require Import List.
Require Import Omega.

Check count_occ.

Lemma count_occ_concat {A}:
  forall (l l' : list A) (a : A) (eq_dec : forall (x y : A), {x = y} + {x <> y}),
  count_occ eq_dec (l ++ l') a = count_occ eq_dec l a + count_occ eq_dec l' a.
Proof.
  intros l l' a eq_dec; induction l as [ | b l].
  + simpl; auto.
  + rewrite <-app_comm_cons; destruct (eq_dec b a).
    - repeat rewrite count_occ_cons_eq by auto; omega.
    - repeat rewrite count_occ_cons_neq by auto; omega.
Qed.

Definition MemoryPool := list bool.

Definition mp_total_size (mp : MemoryPool) : nat := length mp.

Definition mp_occupied_size (mp : MemoryPool) : nat := count_occ Bool.bool_dec mp true.

Definition mp_free_size (mp : MemoryPool) : nat := count_occ Bool.bool_dec mp false.

Fixpoint mp_constant_prefix_len (mp : MemoryPool) (a : bool) : nat :=
  match mp, a with
  | true :: rmp, true => S (mp_constant_prefix_len rmp a)
  | false :: rmp, false => S (mp_constant_prefix_len rmp a)
  | _, _ => 0
  end.

Fixpoint mp_create_uniform_pool (a : bool) (n : nat) : MemoryPool :=
  match n with
  | 0 => nil
  | S m => a :: (mp_create_uniform_pool a m)
  end.

Fixpoint mp_add_constant_prefix (mp : MemoryPool) (n : nat) (a : bool) :=
  match n with
  | 0 => mp
  | S m => a :: (mp_add_constant_prefix mp m a)
  end.

Lemma no_lost_space: 
  forall (mp : MemoryPool),
  mp_total_size mp = mp_occupied_size mp + mp_free_size mp.
Proof.
  induction mp.
  + compute; auto.
  + destruct a; simpl; rewrite IHmp; unfold mp_free_size, mp_occupied_size; simpl; omega.
Qed.

Lemma prefix_smaller_than_whole:
  forall (mp : MemoryPool) (a : bool),
  mp_constant_prefix_len mp a <= mp_total_size mp.
Proof.
  intros mp a; induction mp as [ | b mp].
  + compute; auto.
  + destruct a, b; simpl in *; omega.
Qed.

Lemma uniform_pool_sizes:
  forall (a : bool) (n : nat) (ump : MemoryPool),
  ump = mp_create_uniform_pool a n ->
  mp_total_size ump = n /\
  count_occ Bool.bool_dec ump a = n /\
  count_occ Bool.bool_dec ump (negb a) = 0 /\
  mp_constant_prefix_len ump a = n /\
  mp_constant_prefix_len ump (negb a) = 0.
Proof.
  intros a n ump Hump_eq; rewrite Hump_eq; clear Hump_eq.
  induction n.
  + simpl; auto.
  + destruct a; simpl in *; omega.
Qed.

Lemma add_constant_prefix_works:
  forall (mp pmp : MemoryPool) (n : nat) (a : bool),
  pmp = mp_add_constant_prefix mp n a ->
  count_occ Bool.bool_dec pmp a = count_occ Bool.bool_dec mp a + n /\
  count_occ Bool.bool_dec pmp (negb a) = count_occ Bool.bool_dec mp (negb a).
Proof.
  intros mp pmp n a; revert pmp; induction n; intros pmp Hpmp_eq; rewrite Hpmp_eq.
  + simpl; omega.
  + assert (count_occ Bool.bool_dec (mp_add_constant_prefix mp n a) a =
            count_occ Bool.bool_dec mp a + n) as IHn_match by (apply IHn; auto).
    assert (count_occ Bool.bool_dec (mp_add_constant_prefix mp n a) (negb a) =
            count_occ Bool.bool_dec mp (negb a)) as IHn_fail by (apply IHn; auto).
    destruct a; simpl in *; rewrite IHn_match, Nat.add_succ_r, IHn_fail; auto.
Qed.