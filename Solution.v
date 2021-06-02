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

Lemma body_maxarray: semax_body Vprog Gprog f_maxarray maxarray_spec.
Proof. Admitted.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof. Admitted.

Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog; semax_func_cons body_maxarray; semax_func_cons body_main.
Qed.