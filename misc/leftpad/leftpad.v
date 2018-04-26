Require Import Arith.
Require Import List.

Fixpoint leftpad {A : Type} (l : list A) (n : nat) (p : A) :=
  match n <=? (length l), n with
    | true, 0 => l
    | true, S m => l
    | false, 0 => nil (* not reached *)
    | false, S m => p :: leftpad l m p
  end.

(* unit tests *)
Definition test_empty: leftpad nil 3 42 = 42 :: 42 :: 42 :: nil := eq_refl.
Definition test_longer: leftpad (1 :: 2 :: 3 :: nil) 2 42 = 1 :: 2 :: 3 :: nil := eq_refl.
Definition test_equal: leftpad (1 :: 2 :: 3 :: nil) 3 42 = 1 :: 2 :: 3 :: nil := eq_refl.
Definition test_padded_0: leftpad (1 :: 2 :: 3 :: nil) 4 42 = 42 :: 1 :: 2 :: 3 :: nil := eq_refl.
Definition test_padded_1: leftpad (1 :: 2 :: 3 :: nil) 5 42 = 42 :: 42 :: 1 :: 2 :: 3 :: nil := eq_refl.

(* proof *)

Theorem long_does_not_change:
  forall (A : Type) (l : list A) (n : nat) (p : A),
  n <= length l -> leftpad l n p = l.
Proof.
  intros; unfold leftpad; destruct n.
  + auto.
  + rewrite leb_correct; auto.
Qed.

Theorem short_gets_padded:
  forall (A : Type) (l : list A) (n : nat) (p : A),
  length l <= n -> leftpad l n p = repeat p (n - length l) ++ l.
Proof.
  intros.
  remember (n - length l) as m.
  destruct m.
  + simpl; apply long_does_not_change, Nat.sub_0_le; auto.
  + remember (S m) as mp.
    assert (n = mp + length l) as Hn_elim.
    {
      rewrite plus_comm.
      apply eq_sym, Nat.add_sub_eq_nz; auto.
      rewrite Heqmp; auto.
    }
    rewrite Hn_elim.
    clear H Heqmp Heqm Hn_elim.
    induction mp.
    - simpl; apply long_does_not_change; auto.
    - assert (S mp + length l = S (mp + length l)) as Hsucc by auto.
      rewrite Hsucc; destruct l; simpl in *; rewrite IHmp; auto.
      assert (mp + S (length l) <=? length l = false) as Hcond by
        (apply leb_correct_conv, Nat.lt_lt_add_l; auto).
      rewrite Hcond; auto.
Qed.
