Require Import Omega.

Inductive MemoryPool : Set :=
  | MPEnd : MemoryPool
  | MPEmpty : MemoryPool -> MemoryPool
  | MPFull : MemoryPool -> MemoryPool.

Function MP_len(p : MemoryPool) : nat :=
  match p with
  | MPEnd => 0
  | MPEmpty tail => S (MP_len tail)
  | MPFull tail => S (MP_len tail)
  end.

Function MP_empty_prefix_len(p : MemoryPool) : nat :=
  match p with 
  | MPEmpty tail => S (MP_empty_prefix_len tail)
  | _ => 0
  end.

Function MP_drop_first_n(p : MemoryPool) (n : nat) : MemoryPool :=
  match n, p with
  | 0, _ => p
  | _, MPEnd => MPEnd
  | S m, MPEmpty tail => MP_drop_first_n tail m
  | S m, MPFull tail => MP_drop_first_n tail m
  end.

Function MP_prepend_n_elems(p : MemoryPool) (n : nat) (e : MemoryPool -> MemoryPool) : MemoryPool :=
  match n with
  | 0 => p
  | S m => e (MP_prepend_n_elems p m e)
  end.

Function MP_malloc(p : MemoryPool)( n : nat) : MemoryPool * nat :=
  match le_dec n (MP_empty_prefix_len p) with
  | left _ _ => (MP_prepend_n_elems (MP_drop_first_n p n) n MPFull, 0)
  | right _ _ =>
      match p with
      | MPEnd => (MP_prepend_n_elems p n MPFull, 0)
      | MPEmpty tail => let (q, i) := MP_malloc tail n in (MPEmpty q, S i)
      | MPFull tail => let (q, i) := MP_malloc tail n in (MPFull q, S i)
      end
  end.

Function MP_count_full(p : MemoryPool) : nat :=
  match p with
  | MPEnd => 0
  | MPEmpty tail => MP_count_full tail
  | MPFull tail => S (MP_count_full tail)
  end.

Function MP_count_empty(p : MemoryPool) : nat :=
  match p with
  | MPEnd => 0
  | MPEmpty tail => S (MP_count_empty tail)
  | MPFull tail => MP_count_empty tail
  end.

Lemma ep_len_le_len :
  forall p : MemoryPool,
  MP_empty_prefix_len p <= MP_len p.
Proof.
  induction p; simpl; omega.
Qed.

Lemma empty_p_full_are_all :
  forall p : MemoryPool,
  MP_count_empty p + MP_count_full p = MP_len p.
Proof.
  induction p; simpl; omega.
Qed.

Lemma prepend_full_increases :
  forall (p : MemoryPool) (n : nat),
  MP_count_full (MP_prepend_n_elems p n MPFull) = MP_count_full p + n /\
  MP_count_empty (MP_prepend_n_elems p n MPFull) = MP_count_empty p.
Proof.
  induction n, p; simpl in *; try omega.
Qed.

Lemma drop_succ_first_empty :
  forall (p : MemoryPool) (n : nat),
  MP_drop_first_n (MPEmpty p) (S n) = MP_drop_first_n p n.
Proof.
  auto.
Qed.

Lemma drop_empty_decreases :
  forall (p : MemoryPool) (n : nat),
  n <= MP_empty_prefix_len p ->
  MP_count_full (MP_drop_first_n p n) = MP_count_full p /\
  MP_count_empty (MP_drop_first_n p n) + n = MP_count_empty p.
Proof.
  induction p.
  * destruct n; simpl; omega.
  * destruct n.
    + simpl; omega.
    + rewrite drop_succ_first_empty; simpl; intros.
      assert (MP_count_empty (MP_drop_first_n p n) + n = MP_count_empty p ->
              MP_count_empty (MP_drop_first_n p n) + S n = S (MP_count_empty p)) as Haux by omega.
      split.
      - apply IHp; omega.
      - apply Haux, IHp; omega.
  * intros; simpl in *; assert (n = 0) as n_eq_0 by omega.
    rewrite n_eq_0; simpl; auto.
Qed.

Lemma malloc_increases_full :
  forall (p : MemoryPool) (n : nat),
  MP_count_full (fst (MP_malloc p n)) = MP_count_full p + n.
Proof.
  induction n, p; simpl in *; try omega.
  * induction n; simpl in *; omega.
  * destruct (le_dec (S n) (S (MP_empty_prefix_len p))).
    + simpl in *.
      replace (MP_count_full (MP_prepend_n_elems (MP_drop_first_n p n) n MPFull)) with
              (MP_count_full (MP_drop_first_n p n) + n).
      pose proof prepend_full_increases p n as Haux. omega.