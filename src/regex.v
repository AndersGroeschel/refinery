
Section Regex.
Variable A: Type.
Variable Relation: A -> A -> Prop. 

Inductive star: A -> A -> Prop :=
    | star_equal: forall a,
        star a a
    | star_step: forall a b c,
    (Relation a b) -> (star b c) -> (star a c)
.

Lemma star_one:
    forall a b,
    Relation a b -> star a b.
Proof.
    eauto using star.
Qed.

Lemma star_trans:
    forall a b c,
  star a b -> star b c -> star a c.
Proof.
    intros a b c H.
    generalize dependent c.
    induction H; eauto using star. 
Qed.


End Regex.