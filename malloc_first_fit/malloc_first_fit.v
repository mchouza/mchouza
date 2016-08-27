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
  if le_dec n (MP_empty_prefix_len p) then
    (MP_prepend_n_elems (MP_drop_first_n p n) n MPFull, 0)
  else
      match p with
      | MPEnd => (MP_prepend_n_elems p n MPFull, 0)
      | MPEmpty tail => let (q, i) := MP_malloc tail n in (MPEmpty q, S i)
      | MPFull tail => let (q, i) := MP_malloc tail n in (MPFull q, S i)
      end
  .

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

Lemma drop_empty_prefix :
  forall (p : MemoryPool) (n : nat),
  n <= MP_empty_prefix_len p ->
  MP_count_empty (MP_drop_first_n p n) + n = MP_count_empty p /\
  MP_count_full (MP_drop_first_n p n) = MP_count_full p.
Proof.
  induction p; destruct n; simpl in *; try omega.
  split; try apply IHp; try omega.
  cut (MP_count_empty (MP_drop_first_n p n) + n = MP_count_empty p); try omega.
  apply IHp; try omega.
Qed.

Lemma malloc_empty_beginning :
  forall (p : MemoryPool) (n : nat),
  n <= MP_empty_prefix_len p ->
  MP_malloc p n = (MP_prepend_n_elems (MP_drop_first_n p n) n MPFull, 0).
Proof.
  intros; destruct p; simpl in *.
  * case (le_dec n 0); tauto.
  * case (le_dec n (S (MP_empty_prefix_len p))); tauto.
  * case (le_dec n 0); tauto.
Qed.

Lemma malloc_increases_full :
  forall (p : MemoryPool) (n : nat),
  MP_count_full (fst (MP_malloc p n)) = MP_count_full p + n.
Proof.
  induction p.
  {
    assert (forall n, MP_count_full (MP_prepend_n_elems MPEnd n MPFull) = n) by apply prepend_full_increases.
    intros; simpl; destruct (le_dec n 0), n; simpl; auto.
  } 
  {
    intros; destruct (le_dec n (S (MP_empty_prefix_len p))).
    * intros; rewrite malloc_empty_beginning by (simpl; auto); simpl.
      destruct n.
      + simpl; omega.
      + cut (MP_count_full (MP_prepend_n_elems (MP_drop_first_n p n) (S n) MPFull) =
             MP_count_full (MP_drop_first_n p n) + S n).
        - intros Hcut; rewrite Hcut.
          cut (MP_count_full (MP_drop_first_n p n) = MP_count_full p); try omega.
          apply drop_empty_prefix; omega.
        - apply prepend_full_increases.
    * intros; simpl; destruct (le_dec n (S (MP_empty_prefix_len p))); try tauto.
      rewrite surjective_pairing with (p := MP_malloc p n); simpl.
      apply IHp.
  }
  {
    intros; simpl; destruct (le_dec n 0), n; simpl; try omega.
    rewrite surjective_pairing with (p := MP_malloc p (S n)); simpl.
    apply f_equal, IHp.
  }
Qed.
