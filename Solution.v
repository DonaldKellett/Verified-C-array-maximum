Require Import VST.floyd.proofauto.
Require Import Preloaded.

Lemma list_max_Z_nonneg_spec : forall l,
  Forall (fun x => x >= 0) l ->
  let maximum := list_max_Z l in
  match l with
  | [] => maximum = 0
  | _ => Forall (fun x => x <= maximum) l /\ In maximum l
  end.
Proof. Admitted.

Lemma body_maxarray: semax_body Vprog Gprog f_maxarray maxarray_spec.
Proof. Admitted.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof. Admitted.

Existing Instance NullExtension.Espec.

Lemma prog_correct: semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog; semax_func_cons body_maxarray; semax_func_cons body_main.
Qed.