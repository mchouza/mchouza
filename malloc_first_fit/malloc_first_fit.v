Require Import List.
Require Import Omega.

Section ListExtraProperties.

  Set Implicit Arguments.

  Variable (A : Type).

  Hypothesis eq_dec:
    forall (x y : A), {x = y} + {x <> y}.

  Lemma firstn_short:
    forall (l : list A) (n : nat),
    length l <= n ->
    firstn n l = l.
  Proof.
    induction l.
    + destruct n; simpl; auto.
    + destruct n; simpl; try omega; intros Hlen; rewrite IHl by omega; auto.
  Qed.

  Lemma skipn_long:
    forall (l : list A) (n : nat),
    length l <= n ->
    skipn n l = nil.
  Proof.
    induction l.
    + destruct n; simpl; auto.
    + destruct n; simpl; intros; try apply IHl; omega.
  Qed.

  Lemma app_firstn_1st:
    forall (l l' : list A) (n : nat),
    n <= length l ->
    firstn n (l ++ l') = firstn n l.
  Proof.
    induction l; intros l' n Hn_bound; simpl in *.
    + assert (n = 0) as Hn_eq_0 by omega; rewrite Hn_eq_0; simpl; auto.
    + destruct n; simpl; auto; rewrite IHl by omega; auto.
  Qed.

  Lemma app_skipn_2nd:
    forall (l l' : list A) (n : nat),
    length l <= n ->
    skipn n (l ++ l') = skipn (n - length l) l'.
  Proof.
    induction l; destruct n; simpl; auto; try omega.
    intros; rewrite IHl by omega; auto.
  Qed.

  Lemma skipn_len:
    forall (l : list A) (n : nat),
    n <= length l ->
    length (skipn n l) = length l - n.
  Proof.
    induction l.
    + destruct n; simpl; auto.
    + intros n IHn_bound; destruct n.
      - simpl; auto.
      - simpl in *; apply IHl; omega.
  Qed.

  Lemma count_occ_concat:
    forall (l l' : list A) (a : A),
    count_occ eq_dec (l ++ l') a = count_occ eq_dec l a + count_occ eq_dec l' a.
  Proof.
    intros l l' a; induction l as [ | b l].
    + simpl; auto.
    + rewrite <-app_comm_cons; destruct (eq_dec b a).
      - repeat rewrite count_occ_cons_eq by auto; omega.
      - repeat rewrite count_occ_cons_neq by auto; omega.
  Qed.

  Fixpoint count_not_occ (l : list A) (a : A) : nat :=
    match l with
    | b :: l' =>
      let cnot := count_not_occ l' a in
      if eq_dec a b then cnot else S cnot
    | nil => 0
    end.

  Lemma count_occ_not_occ_total:
    forall (l : list A) (a : A),
    count_occ eq_dec l a + count_not_occ l a = length l.
  Proof.
    intros l a; induction l as [ | b l'].
    + simpl; auto.
    + simpl; destruct (eq_dec b a), (eq_dec a b); simpl; try omega; exfalso; auto.
  Qed.

  Fixpoint uniform_list (a : A) (n : nat) : list A :=
    match n with
    | 0 => nil
    | S m => a :: (uniform_list a m)
    end.

  Fixpoint uniform_prefix_len (l : list A) (a : A) : nat :=
    match l with
    | b :: l' =>
      if eq_dec a b 
      then S (uniform_prefix_len l' a)
      else 0
    | nil => 0
    end.

  Lemma uniform_list_len:
    forall (a : A) (n : nat),
    length (uniform_list a n) = n.
  Proof.
    intros a n; induction n; simpl; omega.
  Qed.

  Lemma uniform_prefix_len_bound:
    forall (l : list A) (a : A),
    uniform_prefix_len l a <= length l.
  Proof.
    intros l a; induction l as [ | b l']; simpl.
    + omega.
    + destruct (eq_dec a b); omega.
  Qed.

  Lemma count_occ_uniform_list:
    forall (a b : A) (n : nat),
    let ul := uniform_list a n in
    count_occ eq_dec ul a = n /\
    (a <> b -> count_occ eq_dec ul b = 0).
  Proof.
    intros a b n ul; subst ul; induction n.
    + simpl; auto.
    + split.
      - simpl; destruct (eq_dec a a); try tauto; omega.
      - intros Hineq; simpl; destruct (eq_dec a b); try tauto.
  Qed.

  Lemma uniform_prefix_can_be_taken:
    forall (l : list A) (a : A),
    let upl := (uniform_prefix_len l a) in
    firstn upl l = uniform_list a upl.
  Proof.
    intros l a upl; subst upl; induction l as [ | b l'].
    + simpl; auto.
    + simpl; destruct (eq_dec a b); simpl; auto.
      rewrite <-e; f_equal; auto.
  Qed.

End ListExtraProperties.

Section MemPoolBasic.

  Inductive MemCell :=
    | FreeCell : MemCell
    | OccupiedCell : MemCell.

  Lemma eq_dec:
    forall (mc mc' : MemCell),
    {mc = mc'} + {mc <> mc'}.
  Proof.
    intros mc mc'; destruct mc, mc'; auto; right; discriminate.
  Qed.

  Definition MemPool := list MemCell.

  Definition mp_count_all (mp : MemPool) : nat :=
    length mp.

  Definition mp_count_free (mp : MemPool) : nat :=
    count_occ eq_dec mp FreeCell.

  Definition mp_count_occupied (mp : MemPool) : nat :=
    count_occ eq_dec mp OccupiedCell.

  Definition mp_count_free_prefix (mp : MemPool) : nat :=
    uniform_prefix_len eq_dec mp FreeCell.

  Lemma all_cells_free_or_occupied:
    forall (mp : MemPool),
    mp_count_free mp = count_not_occ eq_dec mp OccupiedCell /\
    mp_count_occupied mp = count_not_occ eq_dec mp FreeCell.
  Proof.
    induction mp as [| c mp [IHmp IHmp']].
    + simpl; auto.
    + split; unfold mp_count_free, mp_count_occupied in *; simpl; 
        try rewrite IHmp; try rewrite IHmp'; simpl;
        destruct (eq_dec c FreeCell), (eq_dec OccupiedCell c),
                 (eq_dec c OccupiedCell), (eq_dec FreeCell c), c;
        auto; try (exfalso; auto; discriminate).
  Qed.

End MemPoolBasic.

Section MemPoolMallocFirstFit.

  Fixpoint mp_malloc_first_fit_aux (mp : MemPool) (n o : nat) : nat * MemPool :=
    if le_dec n (mp_count_free_prefix mp)
    then (o, (uniform_list OccupiedCell n) ++ (skipn n mp))
    else
      if Nat.eq_dec (mp_count_free_prefix mp) (mp_count_all mp)
      then (o, (uniform_list OccupiedCell n))
      else
        match mp with
        | c :: rmp =>
            let (no, nrmp) := mp_malloc_first_fit_aux rmp n (S o) in
            (S no, c :: nrmp)
        | _ =>
            (0, nil) (* NOT REACHED *)
        end.

  Definition mp_malloc_first_fit (mp : MemPool) (n : nat) : nat * MemPool :=
    mp_malloc_first_fit_aux mp n 0.

  Lemma malloc_first_fit_works:
    forall (mp : MemPool) (n : nat),
    let (o, nmp) := mp_malloc_first_fit mp n in
    firstn n (skipn o nmp) = uniform_list OccupiedCell n /\
    firstn o nmp = firstn o mp /\
    skipn (o + n) (firstn (length mp) nmp) = skipn (o + n) mp.
  Proof.
    intros mp n; unfold mp_malloc_first_fit; induction mp as [ | c rmp]; simpl.
    {
      unfold mp_count_free_prefix; destruct n; simpl; split; auto.
      assert (length (uniform_list OccupiedCell n) = n) by apply uniform_list_len.
      rewrite firstn_short by omega; auto.
    }
    {
      destruct (le_dec n (mp_count_free_prefix (c :: rmp))); simpl;
        assert (length (uniform_list OccupiedCell n) = n) by apply uniform_list_len.
      + rewrite app_firstn_1st, firstn_short by omega.
        destruct n; simpl.
        - rewrite firstn_short by omega; auto.
        - assert (mp_count_free_prefix (c :: rmp) <= length (c :: rmp)) by
            apply uniform_prefix_len_bound.
          assert (length (uniform_list OccupiedCell n ++ skipn n rmp) = length rmp)
            by (rewrite app_length, uniform_list_len, skipn_len; simpl in *; omega).
          assert (length (uniform_list OccupiedCell n) = n) by apply uniform_list_len.
          rewrite firstn_short, app_skipn_2nd by omega.
          rewrite uniform_list_len, Nat.sub_diag; simpl; auto.
      + admit.
    }
  Admitted.

End MemPoolMallocFirstFit.