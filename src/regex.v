Require Import customTactics.
Section Regex.

Definition Relation (A:Type) := A -> A -> Prop. 

Inductive star {A: Type} (R: Relation A): (Relation A) :=
    | star_equal: forall a,
        star R a a
    | star_step: forall a b c,
    (R a b) -> (star R b c) -> (star R a c)
.

Lemma star_one:
    forall {A : Type} (R : Relation A) (a b : A),
    R a b -> star R a b.
Proof.
    intros A R a b H.
    eapply star_step;[apply H| apply star_equal].
Qed.

Lemma star_trans:
    forall {A : Type} (R : Relation A) (a b c : A),
    star R a b -> star R b c -> star R a c.
Proof.
    intros A R a b c H H0.
    induction H;[
        assumption |
        eapply star_step
    ];
    eauto.
Qed.

Lemma star_step_between: 
    forall {A : Type} (R : Relation A) (a b c : A),
    star R a b -> R b c -> star R a c.
Proof.
    intros A R a b c H H0.
    eapply star_trans.
    - apply H.
    - apply star_one. assumption.
Qed. 

Lemma star_relationCommute_starCommute:
    forall {A : Type} (R : Relation A) (a b: A),
    (forall a' b', R a' b' -> R b' a') ->
    star R a b ->
    star R b a.
Proof.
    intros A R a b R_Commutes H.
    induction H;[apply star_equal |].
    eapply star_trans.
    - apply IHstar.
    - apply R_Commutes in H.
        apply star_one; assumption. 
Qed.

Inductive plus {A: Type} (R: Relation A): (Relation A) :=
    | plus_one: forall a b,
        R a b -> plus R a b
    | plus_multi: forall a b c,
        R a b -> plus R b c -> plus R a c
.

Lemma plus_trans:
    forall {A : Type} (R : Relation A) (a b c : A),
    plus R a b -> plus R b c -> plus R a c.
Proof.
    intros A R a b c H H0.
    induction H; eapply (plus_multi); repeat (try applyFromContext; logicAuto).

Qed.


Lemma plus_step_between: 
    forall {A : Type} (R : Relation A) (a b c : A),
    plus R a b -> R b c -> plus R a c.
Proof.
    intros A R a b c H H0.
    eapply plus_trans.
    - apply H.
    - apply plus_one. assumption.
Qed. 

Ltac plusAuto :=
    try solve[do 5 try (
        logicAuto;
        (applyFromContext ||
        multimatch goal with 
        | H: ?R ?a ?b, H0: plus ?R ?b ?c |- plus ?R ?a ?c => 
            eapply (plus_multi); [
                apply H | apply H0
            ]
        | H: plus ?R ?a ?b, H0: ?R ?b ?c |- plus ?R ?a ?c => 
            eapply plus_step_between; [
                apply H | apply H0
            ]
        | H: plus ?R ?a ?b, H0: plus ?R ?b ?c |- plus ?R ?a ?c =>
            eapply plus_trans;[
                apply H | apply H0
            ]
        | H: ?R ?a ?b, H0: ?R ?b ?c |- plus ?R ?a ?c =>
            eapply plus_multi;[
                apply H | apply plus_one; apply H0
            ]
        | H: ?R ?a ?b |- plus ?R ?a ?b => apply plus_one; apply H

        | |- plus _ _ _ => eapply plus_one
        | |- plus _ _ _ => eapply plus_multi
        | |- plus _ _ _ => eapply plus_step_between
        | |- plus _ _ _ => eapply plus_trans
        end
    ))].



Lemma plus_relationCommute_plusCommute:
    forall {A : Type} (R : Relation A) (a b: A),
    (forall a' b', R a' b' -> R b' a') ->
    plus R a b ->
    plus R b a.
Proof.
    intros A R a b R_Commutes H.
    induction H; plusAuto.
Qed.


Lemma plus_inversion:
    forall {A : Type} (R : Relation A) (a b: A), 
    (plus R a b) ->
    (R a b) \/ 
    (
        (exists c, (plus R a c) /\ (R c b)) /\ 
        (exists d, (R a d) /\ (plus R d b))
    ).
Proof.
    intros A R a b H.
    induction H; subst; plusAuto.
    - right. plusAuto.
Qed.


Ltac invertPlus H :=
    apply plus_inversion in H; logicAuto.


End Regex.