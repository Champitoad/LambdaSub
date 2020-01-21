Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X} (R : relation X) : relation X :=
| multi_refl x :
  multi R x x
| multi_step x y z :
  R x y -> multi R y z -> multi R x z.

Lemma multi_trans {X} (R : relation X) : forall x y z,
  multi R x y -> multi R y z -> multi R x z.
Proof.
  induction 1.
  * easy.
  * intro. eapply multi_step; eauto.
Qed.

Definition normal_form {X} (R : relation X) (x : X) : Prop :=
  ~ exists y, R x y.
