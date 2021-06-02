Require Import VST.floyd.proofauto.
Require Import Preloaded.

Lemma fold_right_Z_max_spec : forall l x0,
  let max_val := fold_right Z.max x0 l in
  Forall (fun x => x <= max_val) l /\
  (In max_val l \/ max_val = x0).
Proof.
  induction l; intros; split; auto; subst max_val; simpl in *.
  - apply Forall_cons.
    + apply Z.le_max_l.
    + destruct (IHl x0) as [H _].
      eapply Forall_impl; try eapply H; simpl; intros x Hx.
      rewrite Z.max_le_iff; auto.
  - destruct (IHl (Z.max a x0)) as [H0 [H1 | H2]].
    + rewrite <- (fold_symmetric _ Z.max_assoc (Z.max a x0) (Z.max_comm _)),
        Z.max_comm in H1.
      assert (H2 : fold_left Z.max l (Z.max x0 a) = fold_left Z.max (a :: l) x0)
        by reflexivity.
      rewrite H2 in H1; clear H2.
      rewrite (fold_symmetric _ Z.max_assoc x0 (Z.max_comm _)) in H1; simpl in H1;
        auto.
    + destruct (Z.max_dec a x0) as [H3 | H3].
      * do 2 left.
        assert (H4 : Z.max a (fold_right Z.max x0 l) = fold_right Z.max x0
          (a :: l)) by reflexivity.
        rewrite H4; clear H4.
        rewrite <- (fold_symmetric _ Z.max_assoc x0 (Z.max_comm _)); simpl.
        rewrite Z.max_comm, (fold_symmetric _ Z.max_assoc (Z.max a x0)
          (Z.max_comm _)); congruence.
      * right.
        assert (H4 : Z.max a (fold_right Z.max x0 l) = fold_right Z.max x0
          (a :: l)) by reflexivity.
        rewrite H4; clear H4.
        rewrite <- (fold_symmetric _ Z.max_assoc x0 (Z.max_comm _)); simpl.
        rewrite Z.max_comm, (fold_symmetric _ Z.max_assoc (Z.max a x0)
          (Z.max_comm _)); congruence.
Qed.

Lemma list_max_Z_spec : forall l,
  let max_val := list_max_Z l in
  Forall (fun x => x <= max_val) l /\
  (In max_val l \/ max_val = 0).
Proof. intros l; exact (fold_right_Z_max_spec l 0). Qed.

Lemma list_max_Z_nonneg_spec : forall l,
  Forall (fun x => x >= 0) l ->
  let maximum := list_max_Z l in
  match l with
  | [] => maximum = 0
  | _ => Forall (fun x => x <= maximum) l /\ In maximum l
  end.
Proof.
  intros l Hl; simpl.
  destruct l; auto.
  destruct (list_max_Z_spec (z :: l)) as [H0 [H1 | H2]]; split; auto; simpl in *.
  rewrite H2 in *; apply Forall_inv in Hl; apply Forall_inv in H0; lia.
Qed.

Lemma Zmax_0_list_max_Z : forall l,
  Z.max 0 (list_max_Z l) = list_max_Z l.
Proof.
  induction l; simpl; auto.
  rewrite Z.max_assoc, (Z.max_comm 0 a), <- Z.max_assoc; congruence.
Qed.

Lemma list_max_Z_app : forall l0 l1,
  list_max_Z (l0 ++ l1) = Z.max (list_max_Z l0) (list_max_Z l1).
Proof.
  induction l0; intros l1; simpl.
  - now rewrite Zmax_0_list_max_Z.
  - now rewrite IHl0, Z.max_assoc.
Qed.

Lemma body_maxarray: semax_body Vprog Gprog f_maxarray maxarray_spec.
Proof.
  start_function.
  do 2 forward.
  forward_while
  (EX i: Z,
   PROP (0 <= i <= size)
   LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _m (Vint (Int.repr (list_max_Z (sublist 0 i contents)))))
   SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
  - Exists 0.
    entailer!.
  - entailer!.
  - assert_PROP (Zlength (map Int.repr contents) = size)
      by (entailer!; list_solve).
    autorewrite with sublist in *|-.
    forward.
    forward_if (
      PROP ()
      LOCAL (temp _t'1 (Vint (Int.repr (Znth i contents))); 
        temp _a a; temp _i (Vint (Int.repr i));
        temp _n (Vint (Int.repr size));
        temp _m (Vint (Int.repr (list_max_Z (sublist 0 (i + 1) contents)))))
      SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
    + forward.
      entailer!.
      autorewrite with sublist in *|-.
      do 2 f_equal.
      assert (H6 : 0 <= list_max_Z (sublist 0 i contents) <= Int.max_unsigned).
      { apply (Forall_sublist _ 0 i) in H0.
        assert (H6 : forall x, (fun x => 0 <= x <= Int.max_unsigned) x ->
          (fun x => x >= 0) x) by lia.
        assert (H7 := @Forall_impl _ _ _ H6 _ H0).
        assert (H8 := list_max_Z_nonneg_spec _ H7); simpl in H8.
        destruct (sublist 0 i contents) eqn:Esub; simpl; try rep_lia.
        simpl in H8; destruct H8 as [H8 H9].
        destruct H9 as [H9 | H9].
        - apply Forall_inv in H0; now rewrite <- H9.
        - apply Forall_inv_tail in H0; rewrite Forall_forall in H0; auto. }
      do 2 rewrite Int.unsigned_repr in H3; try apply H6.
      * rewrite sublist_last_1; try lia.
        rewrite list_max_Z_app; simpl.
        assert (In (Znth i contents) contents) by (apply Znth_In; lia).
        rewrite Forall_forall in H0.
        assert (H8 := H0 _ H7).
        assert (H9 : Znth i contents >= 0) by lia.
        apply Zmax_left in H9; rewrite H9.
        assert (H10 : list_max_Z (sublist 0 i contents) <= Znth i contents) by lia.
        now rewrite Zmax_right.
      * assert (H7 : 0 <= i < Zlength contents) by lia.
        apply Znth_In in H7; rewrite Forall_forall in H0; auto.
    + forward.
      entailer!.
      autorewrite with sublist in *|-.
      do 2 f_equal.
      assert (H6 : 0 <= list_max_Z (sublist 0 i contents) <= Int.max_unsigned).
      { apply (Forall_sublist _ 0 i) in H0.
        assert (H6 : forall x, (fun x => 0 <= x <= Int.max_unsigned) x ->
          (fun x => x >= 0) x) by lia.
        assert (H7 := @Forall_impl _ _ _ H6 _ H0).
        assert (H8 := list_max_Z_nonneg_spec _ H7); simpl in H8.
        destruct (sublist 0 i contents) eqn:Esub; simpl; try rep_lia.
        simpl in H8; destruct H8 as [H8 H9].
        destruct H9 as [H9 | H9].
        - apply Forall_inv in H0; now rewrite <- H9.
        - apply Forall_inv_tail in H0; rewrite Forall_forall in H0; auto. }
      do 2 rewrite Int.unsigned_repr in H3; try apply H6.
      * rewrite sublist_last_1; try lia.
        rewrite list_max_Z_app; simpl.
        assert (In (Znth i contents) contents) by (apply Znth_In; lia).
        rewrite Forall_forall in H0.
        assert (H8 := H0 _ H7).
        assert (H9 : Znth i contents >= 0) by lia.
        apply Zmax_left in H9; rewrite H9.
        assert (H10 : Znth i contents <= list_max_Z (sublist 0 i contents)) by lia.
        now rewrite Zmax_left.
      * assert (H7 : 0 <= i < Zlength contents) by lia.
        apply Znth_In in H7; rewrite Forall_forall in H0; auto.
    + forward.
      Exists (i + 1).
      entailer!.
  - forward.
    autorewrite with sublist.
    autorewrite with sublist in *|-.
    assert (H4 : 0 = 0) by reflexivity.
    assert (H5 : i = Zlength contents) by lia.
    rewrite (@sublist_same _ _ _ _ H4 H5).
    entailer!.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  autorewrite with norm.
  forward_call (gv _myarr, Ews, [1; 4; 2; 3], 4); repeat split; auto;
    repeat constructor; try rep_lia.
  autorewrite with norm; forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog; semax_func_cons body_maxarray; semax_func_cons body_main.
Qed.