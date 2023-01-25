Require Import ZArith.


Ltac unifyAssumption := multimatch goal with 
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

Ltac assertIfNonExistent H :=
    lazymatch goal with 
    | H': H |- _ => fail
    | |- _ => assert (H)
    end.

Ltac assertIfNonExistentNamed H name :=
    lazymatch goal with 
    | H': H |- _ => fail
    | |- _ => assert (H) as name
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


Ltac solvebyInvert := 
    match goal with 
    | H: _ |- _ => solve[
        inversion H; subst;
        (reflexivity || unifyAssumption || contradiction || discriminate || congruence)
        ]
    end.


Ltac logicAuto :=
    repeat (
        simpl in *; 
        (match goal with 
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
        | |- _ \/ _ =>  solve[((repeat (solve[left; logicAuto ] || right)); logicAuto)]
        | |- exists _, _ => eexists 
        | |- context [if ?b then _ else _]  => let eq :=  fresh "eq" in destruct b eqn: eq
        end ||
        solvebyInvert ||
        reflexivity || contradiction || discriminate || congruence
        )
    )
.


Ltac applyFromContext := 
    multimatch goal with 
    | H: _ -> ?P |- ?P => eapply H
    | H: forall _,  _ -> ?P |- ?P => eapply H
    | H: forall _ _,  _ -> ?P |- ?P => eapply H
    | H: forall _ _ _,  _ -> ?P |- ?P => eapply H

    | H: forall _,  _ -> ?P _ |- ?P _ => eapply H
    | H: forall _ _,  _ -> ?P _ |- ?P _ => eapply H
    | H: forall _ _ _,  _ -> ?P _ |- ?P _ => eapply H

    | H: forall _,  _ -> ?P _ _ |- ?P _ _ => eapply H
    | H: forall _ _,  _ -> ?P _ _ |- ?P _ _ => eapply H
    | H: forall _ _ _,  _ -> ?P _ _ |- ?P _ _ => eapply H

    | H: forall _,  _ -> ?P _ _ _ |- ?P _ _ _ => eapply H
    | H: forall _ _,  _ -> ?P _ _ _ |- ?P _ _ _ => eapply H
    | H: forall _ _ _,  _ -> ?P _ _ _ |- ?P _ _ _ => eapply H
end.



