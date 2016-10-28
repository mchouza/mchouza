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

  Lemma app_firstn_2nd:
    forall (l l' : list A) (n : nat),
    length l <= n ->
    firstn n (l ++ l') = l ++ (firstn (n - length l) l').
  Proof.
    induction l; intros l' n Hn_bound; simpl in *.
    + assert (n - 0 = n) as Hn_minus_0 by omega; rewrite Hn_minus_0; simpl; auto.
    + destruct n; simpl; try omega; rewrite IHl by omega; auto.
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

  Lemma uniform_prefix_drop:
    forall (l : list A) (a : A) (n : nat),
    uniform_prefix_len l a = S n ->
    uniform_prefix_len (skipn 1 l) a = n.
  Proof.
    induction l as [ | b l'].
    + simpl; intros; omega.
    + intros a n; simpl; destruct (eq_dec a b); omega.
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
            let (no, nrmp) := mp_malloc_first_fit_aux rmp n o in
            (S no, c :: nrmp)
        | nil =>
            (o, nil) (* NOT REACHED *)
        end.

  Definition mp_malloc_first_fit (mp : MemPool) (n : nat) : nat * MemPool :=
    mp_malloc_first_fit_aux mp n 0.

  Lemma offset_bigger_than_base:
    forall (mp : MemPool) (n bo : nat),
    let (o, nmp) := mp_malloc_first_fit_aux mp n bo in
    bo <= o.
  Proof.
    induction mp as [ | c rmp]; simpl.
    + intros; destruct (le_dec _ _); auto.
    + intros; destruct (le_dec _ _); simpl; auto.
      destruct (Nat.eq_dec _ _); simpl; auto.
      specialize (IHrmp n bo).
      remember (mp_malloc_first_fit_aux _ _ _) as malloc_rec.
      destruct malloc_rec as (o, nrmp).
      omega.
  Qed.

  Lemma mffaw_fits_beginning:
    forall (rmp : MemPool) (c : MemCell) (n : nat),
    firstn n (skipn 0 (uniform_list OccupiedCell n ++ skipn n (c :: rmp))) =
    uniform_list OccupiedCell n /\
    firstn 0 (uniform_list OccupiedCell n ++ skipn n (c :: rmp)) = firstn 0 (c :: rmp) /\
    skipn n (firstn (length (c :: rmp)) (uniform_list OccupiedCell n ++ skipn n (c :: rmp))) =
    skipn n (c :: rmp).
  Proof.
    intros; simpl.
    assert (length (uniform_list OccupiedCell n) = n) by apply uniform_list_len.
    assert (n - length (uniform_list OccupiedCell n) = 0) as Hlen_sub by omega.
    rewrite app_firstn_1st, firstn_short by omega.
    destruct n; simpl in *.
    + rewrite firstn_short; auto.
    + destruct (le_dec n (length rmp)).
      - rewrite app_firstn_2nd, app_skipn_2nd, Hlen_sub by omega; simpl.
        rewrite firstn_short; auto.
        rewrite skipn_len, uniform_list_len; auto.
      - assert (skipn n rmp = nil) as Hskipn_is_nil by
          (rewrite skipn_long by omega; auto).
        rewrite skipn_long, Hskipn_is_nil; auto.
        rewrite app_firstn_1st.
        * rewrite firstn_length, Min.le_min_l; omega.
        * rewrite uniform_list_len; omega.
  Qed.

  Lemma mffaw_at_end:
    forall (rmp : MemPool) (c : MemCell) (n : nat),
    ~ n <= mp_count_free_prefix (c :: rmp) ->
    mp_count_free_prefix (c :: rmp) = S (mp_count_all rmp) ->
    firstn n (skipn 0 (uniform_list OccupiedCell n)) = uniform_list OccupiedCell n /\
    firstn 0 (uniform_list OccupiedCell n) = firstn 0 (c :: rmp) /\
    skipn n (firstn (length (c :: rmp)) (uniform_list OccupiedCell n)) = skipn n (c :: rmp).
  Proof.
    unfold mp_count_all, mp_count_free_prefix; intros; simpl.
    assert (length (uniform_list OccupiedCell n) = n) by apply uniform_list_len.
    assert (uniform_prefix_len eq_dec (c :: rmp) FreeCell <= length (c :: rmp)) by
      apply uniform_prefix_len_bound.
    assert (length (c :: rmp) = S (length rmp)) by auto.
    destruct (uniform_list OccupiedCell n); simpl length in *; try omega.
    rewrite firstn_short; repeat rewrite skipn_long; simpl; auto; try omega.
    rewrite firstn_length, Min.min_l; omega.
  Qed.

  Lemma mffaw_rec:
    forall (rmp nrmp : MemPool) (c : MemCell) (bo no n : nat),
    bo <= no ->
    (firstn n (skipn (no - bo) nrmp) = uniform_list OccupiedCell n /\
     firstn (no - bo) nrmp = firstn (no - bo) rmp /\
     skipn (no + n - bo) (firstn (length rmp) nrmp) = skipn (no + n - bo) rmp) ->
    firstn n (skipn (S no - bo) (c :: nrmp)) = uniform_list OccupiedCell n /\
    firstn (S no - bo) (c :: nrmp) = firstn (S no - bo) (c :: rmp) /\
    skipn (S no + n - bo) (firstn (length (c :: rmp)) (c :: nrmp)) =
    skipn (S no + n - bo) (c :: rmp).
  Proof.
    intros rmp nrmp c bo no n Hbo_le_no Hind; simpl length.
    assert (S no - bo = S (no - bo)) as Hnobo by omega.
    assert (S no + n - bo = S (no + n - bo)) as Hnonbo by omega.
    assert (firstn (S (length rmp)) (c :: nrmp) = c :: firstn (length rmp) nrmp) as Hfirstn
      by (simpl; auto).
    rewrite Hnobo, Hnonbo, Hfirstn; simpl.
    destruct Hind as [Hind1 [Hind2 Hind3]].
    repeat split; auto; f_equal; auto.
  Qed.

  Lemma malloc_first_fit_aux_works:
    forall (mp : MemPool) (n bo : nat),
    let (o, nmp) := mp_malloc_first_fit_aux mp n bo in
    firstn n (skipn (o - bo) nmp) = uniform_list OccupiedCell n /\
    firstn (o - bo) nmp = firstn (o - bo) mp /\
    skipn (o + n - bo) (firstn (length mp) nmp) = skipn (o + n - bo) mp.
  Proof.
    assert (forall bo, bo - bo = 0) as Hbo by (intros; omega).
    assert (forall bo n, bo + n - bo = n) as Hbon by (intros; omega).
    assert (forall n, length (uniform_list OccupiedCell n) <= n) as Hlen by
      (intros; rewrite uniform_list_len; omega).
    induction mp as [ | c rmp]; simpl mp_malloc_first_fit_aux.
    + intros; rewrite skipn_long, app_nil_r by (simpl; omega).
      destruct (le_dec _ _);
        rewrite Hbo, Hbon, firstn_short by apply Hlen; simpl; auto.
    + intros; destruct (le_dec _ _).
      - rewrite Hbo, Hbon; apply mffaw_fits_beginning.
      - destruct (Nat.eq_dec _ _).
        * rewrite Hbo, Hbon; apply mffaw_at_end; auto.
        * remember (mp_malloc_first_fit_aux _ _ _) as rec.
          specialize (IHrmp n bo).
          destruct rec as (no, nrmp) in *.
          rewrite <-Heqrec in IHrmp.
          apply mffaw_rec; auto.
          assert (let (no, nrmp) := mp_malloc_first_fit_aux rmp n bo in bo <= no)
            by apply offset_bigger_than_base.
          destruct (mp_malloc_first_fit_aux rmp n bo) as (no', nrmp').
          inversion Heqrec; auto.
  Qed.

  Lemma malloc_first_fit_works:
    forall (mp : MemPool) (n : nat),
    let (o, nmp) := mp_malloc_first_fit mp n in
    firstn n (skipn o nmp) = uniform_list OccupiedCell n /\
    firstn o nmp = firstn o mp /\
    skipn (o + n) (firstn (length mp) nmp) = skipn (o + n) mp.
  Proof.
    intros; unfold mp_malloc_first_fit.
    remember (mp_malloc_first_fit_aux _ _ _) as tmp.
    pose (malloc_first_fit_aux_works mp n 0) as H.
    destruct tmp as (o, nmp) in *.
    rewrite <-Heqtmp in H.
    assert (o = o - 0) as Ho by omega.
    assert ((o - 0) + n = o + n - 0) as Hon by omega.
    rewrite Ho, Hon.
    apply H.
  Qed.

  Lemma malloc_first_fit_doesnt_skip_aux:
    forall (mp : MemPool) (n fo bo : nat),
    n <= mp_count_free_prefix (skipn fo mp) ->
    fst (mp_malloc_first_fit_aux mp n bo) <= bo + fo.
  Proof.
    unfold mp_malloc_first_fit, mp_count_free_prefix; induction mp.
    + destruct fo; simpl; intros; assert (n = 0) as Hn_eq_0 by omega.
      rewrite Hn_eq_0; simpl; auto; omega.
      destruct (le_dec _ _); simpl; omega.
    + intros n fo; simpl; destruct (le_dec n (mp_count_free_prefix (a :: mp))).
      - simpl; intros; omega.
      - destruct (Nat.eq_dec _ _); simpl; intros; try omega.
        unfold mp_count_free_prefix in *.
        destruct fo as [ | fo']; simpl skipn in *; try omega.
        remember (mp_malloc_first_fit_aux _ _ _) as rec.
        destruct rec as [no nrmp]; simpl.
        specialize (IHmp n fo' bo H).
        rewrite <-Heqrec in *; simpl in *; omega.
  Qed.

  Lemma malloc_first_fit_doesnt_skip:
    forall (mp : MemPool) (n fo : nat),
    n <= mp_count_free_prefix (skipn fo mp) ->
    fst (mp_malloc_first_fit mp n) <= fo.
  Proof.
    intros mp n fo H.
    pose (malloc_first_fit_doesnt_skip_aux (n := n) mp fo 0 H) as Hbase.
    simpl in *; auto.
  Qed.

End MemPoolMallocFirstFit.