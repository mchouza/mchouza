Require Import List.
Require Import ZArith.

Open Scope Z.

Fixpoint is_in (a : Z) (l : list Z) :=
  match l with
    | h :: t => if a =? h then true else is_in a t
    | nil => false
  end.

Fixpoint unique (l : list Z) :=
  match l with
    | h :: t => if is_in h t then unique t else h :: unique t
    | nil => nil
  end.

Definition unique_empty: unique nil = nil := eq_refl.
Definition unique_already: unique (1 :: 2 :: 3 :: nil) = (1 :: 2 :: 3 :: nil) := eq_refl.
Definition unique_nontrivial: unique (3 :: 2 :: 1 :: 2 :: 3 :: nil) = (1 :: 2 :: 3 :: nil) := eq_refl.

Lemma is_in_works:
  forall (a : Z) (l : list Z),
  In a l <-> is_in a l = true.
Proof.
  intros a l; induction l as [|h].
  + simpl; split; auto; discriminate.
  + destruct (Z_eq_dec a h) as [Heq | Hne].
    - rewrite Heq; simpl; rewrite Z.eqb_refl; split; auto.
    - assert (a =? h = false) as Heq_false by (apply Z.eqb_neq; auto).
      simpl; rewrite Heq_false; split.
      * intros [Heq | Hin].
        absurd (h = a); auto.
        apply IHl; auto.
      * intros; right; apply IHl; auto.
Qed.

Theorem no_elems_lost_or_gained:
  forall (l : list Z) (a : Z),
  In a l <-> In a (unique l).
Proof.
  intros; induction l; simpl in *; split; auto.
  + intros [Hh | Ht].
    - rewrite Hh; remember (is_in a l) as cond; destruct cond.
      * apply IHl, is_in_works; auto.
      * apply in_eq.
    - destruct (is_in a0 l).
      * apply IHl, Ht.
      * apply in_cons, IHl, Ht.
  + intros; destruct (is_in a0 l) in H.
    - right; apply IHl, H.
    - destruct (Z_eq_dec a a0).
      * auto.
      * rewrite IHl; apply in_inv; auto.
Qed.

Theorem no_elem_repeated:
  forall (a : Z) (l : list Z),
  (count_occ Z_eq_dec (unique l) a <= 1)%nat.
Proof.
  intros a l; induction l as [|h t]; simpl; auto.
  remember (is_in h t) as h_in_tail; destruct h_in_tail; simpl; auto.
  destruct (Z.eq_dec h a); simpl.
  + assert (count_occ Z.eq_dec (unique t) a = 0%nat) as Hnull_count.
    - apply count_occ_not_In; intro Hin_unique; apply no_elems_lost_or_gained in Hin_unique;
        rewrite e in *.
      absurd (true = is_in a t).
      * rewrite <-Heqh_in_tail; discriminate.
      * apply eq_sym, is_in_works; auto.
    - rewrite Hnull_count; auto.
  + auto.
Qed.