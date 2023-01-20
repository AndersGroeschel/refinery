Require Import ZArith.


Ltac unifyAssumption := match goal with 
| H: ?P |- ?P' => unify P P'; apply H
end.

Ltac solveWithConstructor C := 
    solve [
        eapply C;
        unifyAssumption
    ]
.

Ltac notHypothesis H :=
    lazymatch goal with 
    | H': H |- _ => fail
    | |- _ => try fail
    end.

Ltac flipRelations := 
    match goal with 
    | H: _ = _ |- _ => symmetry in H 
    | H: _ <> _ |- _ => apply not_eq_sym in H
    | H: _ > _ |- _ => apply Z.gt_lt_iff in H
    | H: _ < _ |- _ => apply Z.gt_lt_iff in H
    | H: _ >= _ |- _ => apply Z.ge_le_iff in H
    | H: _ <= _ |- _ => apply Z.ge_le_iff in H
end.

Ltac ObviousMatches solver := 
    match goal with 
    | H : False |- _ => contradiction H
    | H : True |- _ => clear H 
    | H : _ \/ _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H: ?a = ?a |- _ => clear H
    | H: exists _, _ |- _ => destruct H
    | H: (_,_) = (_,_) |- _ => inversion H;subst
    | H: ?P |- ?P' => solve [unify P P'; apply H]
    | H: ?a = ?b |- _ => (rewrite -> H in * || rewrite <- H in *); clear H
    | |- _ /\ _ => split
    | |- _ \/ _ =>  solve[((repeat (solve[left; solver] || right)); solver)]
    | |- exists _, _ => eexists 
    | |- context [if ?b then _ else _]  => let eq := fresh "eq" in destruct b eqn: eq
    end.

Ltac logicAuto_NoSpecialize :=
    repeat (
        simpl in *; 
        (try reflexivity || assumption || contradiction || discriminate);
        (ObviousMatches logicAuto_NoSpecialize))
.

Ltac logicAuto :=
    repeat (
        (ObviousMatches logicAuto) ||
        match goal with 
        | H: ?P, IH: ?P -> _ |- _ => specialize (IH H)
        end
    ).

