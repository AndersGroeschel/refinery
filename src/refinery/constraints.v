Require Import definitions.
Require Import Bool.
Require Import ZArith.
Require Import customTactics.

Local Open Scope Z_scope.

(*  the constraits part of the language is maybe the most important 
    thing to understand. This is how refinemnents are made to base types.
    We constrain the type by applying operators onto the properties of 
    that type, for example true would have the constraint that self = true.
    *)


(* the property of a type that we are constraining *)
Inductive C_Lang_Property : Type := 
    | C_Prop_Self: C_Lang_Property
.
(* check if properties are the same *)
Definition propertiesSame prop1 prop2 := 
match (prop1, prop2) with 
    | (C_Prop_Self,C_Prop_Self) => true
end.

(* relationships properties can have ex: prop = 7 *)
Inductive C_Lang_Operator: Type :=
| C_Op_Equal
| C_Op_NotEqual
| C_Op_LessThan
| C_Op_LessThanEqual
| C_Op_GreaterThan
| C_Op_GreaterThanEqual
.

(* take a relationship and do the oposite*)
Definition negateOp op :=
    match op with 
    | C_Op_Equal => C_Op_NotEqual
    | C_Op_NotEqual => C_Op_Equal
    | C_Op_LessThan => C_Op_GreaterThanEqual
    | C_Op_LessThanEqual => C_Op_GreaterThan
    | C_Op_GreaterThan => C_Op_LessThanEqual
    | C_Op_GreaterThanEqual => C_Op_LessThan
    end.

Definition cOpsEqual op1 op2 := 
    match (op1, op2) with 
    | (C_Op_Equal,C_Op_Equal) => true
    | (C_Op_NotEqual,C_Op_NotEqual) => true
    | (C_Op_LessThan,C_Op_LessThan) => true
    | (C_Op_LessThanEqual,C_Op_LessThanEqual) => true
    | (C_Op_GreaterThan,C_Op_GreaterThan) => true
    | (C_Op_GreaterThanEqual,C_Op_GreaterThanEqual) => true
    | _ => false
    end.

Definition simpleConstraint := (C_Lang_Property * (C_Lang_Operator * R_Lang_Primitive))%type.

(* this is the core of the constraints language
    a type can either have no constraint or a single constraint *)
Inductive Constraints_Lang: Type :=
| C_NoConstraint: Constraints_Lang
| C_Constraint: simpleConstraint -> Constraints_Lang
| C_And: Constraints_Lang -> Constraints_Lang -> Constraints_Lang
| C_Or: Constraints_Lang -> Constraints_Lang -> Constraints_Lang
.

Declare Custom Entry constraint.

Notation " t '[-' x '-]' " := (t,x) (at level 0, x custom constraint at level 99).
Notation "( x )" := x (in custom constraint, x at level 99).
Notation "x" := x (in custom constraint at level 0, x constr at level 0).
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom constraint at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9).

Notation " 'Any' " := C_NoConstraint (in custom constraint).
Notation " 'self' " := C_Prop_Self (in custom constraint).
Notation " 'true' " := (R_Prim_Bool true) (in custom constraint).
Notation " 'false' " := (R_Prim_Bool false) (in custom constraint).
Notation " 'Bool' b " :=  (R_Prim_Bool b) (in custom constraint at level 60, no associativity).
Notation " 'Int' z " :=  (R_Prim_Int z) (in custom constraint at level 60, no associativity).

Notation "x && y"  := (C_And x y) (in custom constraint at level 80, left associativity).
Notation "x || y"  := (C_Or x y) (in custom constraint at level 80, left associativity).

Notation " prop '==' prim " := (C_Constraint (prop, (C_Op_Equal, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '!=' prim " := (C_Constraint (prop, (C_Op_NotEqual, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '<' prim " := (C_Constraint (prop, (C_Op_LessThan, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '>' prim " := (C_Constraint (prop, (C_Op_GreaterThan, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '<=' prim " := (C_Constraint (prop, (C_Op_LessThanEqual, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '>=' prim " := (C_Constraint (prop, (C_Op_GreaterThanEqual, prim))) (in custom constraint at level 70, no associativity).


Definition IsNumberType prim := match prim with 
| R_Prim_Int _ => True 
| _ => False
end.

Definition PrimLe prim1 prim2 := match (prim1, prim2) with 
| (R_Prim_Int z1, R_Prim_Int z2) => z1 < z2
| _ => False
end.

Definition PrimGe prim1 prim2 := match (prim1, prim2) with 
| (R_Prim_Int z1, R_Prim_Int z2) => z1 > z2
| _ => False
end.

Reserved Notation "a 'elementOf' C" (at level 40).
Inductive C_ElementOf_Rules: R_Lang_Primitive -> Refinery_BaseType * Constraints_Lang -> Prop :=
| C_ElementOf_NoConstraint: forall a t,
    t = baseTypeOf a ->
    a elementOf t [- Any -]

| C_ElementOf_Equal: forall a t,
    t = baseTypeOf a ->
    a elementOf t [- self == a -]

| C_ElementOf_And: forall a C1 C2 t,
    t = baseTypeOf a ->
    a elementOf t [- C1 -] ->
    a elementOf t [- C2 -] ->
    a elementOf t [- C1 && C2 -]

| C_ElementOf_Or_Left: forall a C1 C2 t,
    t = baseTypeOf a ->
    a elementOf t [- C1 -] ->
    a elementOf t [- C1 || C2 -]

| C_ElementOf_Or_Right: forall a C1 C2 t,
    t = baseTypeOf a ->
    a elementOf t [- C2 -] ->
    a elementOf t [- C1 || C2 -]

| C_ElementOf_NotEqual: forall a b t,
    t = baseTypeOf a ->
    t = baseTypeOf b ->
    a <> b ->
    a elementOf t [- self != b -]

| C_ElementOf_Le: forall prim1 prim2 t,
    t = baseTypeOf prim1 ->
    t = baseTypeOf prim2 ->
    PrimLe prim1 prim2 ->
    prim1 elementOf t [- self < prim2 -]
| C_ElementOf_LeEq: forall prim1 prim2 t,
    t = baseTypeOf prim1 ->
    t = baseTypeOf prim2 ->
    IsNumberType prim2 ->
    PrimLe prim1 prim2 \/ (prim1 = prim2) ->
    prim1 elementOf t [- self <= prim2 -]

| C_ElementOf_Ge: forall prim1 prim2 t,
    t = baseTypeOf prim1 ->
    t = baseTypeOf prim2 ->
    PrimGe prim1 prim2 ->
    prim1 elementOf t [- self > prim2 -]
| C_ElementOf_GeEq: forall prim1 prim2 t,
    t = baseTypeOf prim1 ->
    t = baseTypeOf prim2 ->
    IsNumberType prim2 ->
    PrimGe prim1 prim2 \/ (prim1 = prim2) ->
    prim1 elementOf t [- self >= prim2 -]

where "a 'elementOf' C" := (C_ElementOf_Rules a C). 

Definition nonEmpty C := exists a, a elementOf C.

Theorem typingMatters:
    forall a t C,
    a elementOf t [- C -] ->
    baseTypeOf a = t.
Proof.
    intros a t C H_elem.
    inversion H_elem; subst; try (reflexivity || assumption).
Qed.

Ltac ElementOfContstuctor := 
    multimatch goal with 
    | |- _ elementOf _ [- Any -] => apply C_ElementOf_NoConstraint
    | |- _ elementOf _ [- self == _ -] => eapply C_ElementOf_Equal
    | |- _ elementOf _ [- _ && _ -] => eapply C_ElementOf_And
    | |- _ elementOf _ [- _ || _ -] => eapply C_ElementOf_Or_Left
    | |- _ elementOf _ [- _ || _ -] => eapply C_ElementOf_Or_Right
    | |- _ elementOf _ [- self != _ -] => eapply C_ElementOf_NotEqual
    | |- _ elementOf _ [- self < _ -] => eapply C_ElementOf_Le
    | |- _ elementOf _ [- self <= _ -] => eapply C_ElementOf_LeEq
    | |- _ elementOf _ [- self > _ -] => eapply C_ElementOf_Ge
    | |- _ elementOf _ [- self >= _ -] => eapply C_ElementOf_GeEq
    end.


Reserved Notation "C1 'satisfies' C2" (at level 40).
Inductive C_Satisfy_Rules: Refinery_BaseType * Constraints_Lang -> Refinery_BaseType * Constraints_Lang -> Prop :=

| C_Satisfies_Equal: forall C t,
    t [- C -] satisfies t [- C -]
| C_Satisfies_Any: forall C t,
    t [- C -] satisfies t [- Any -]

| C_Satisfies_NeqBool: forall b C prop,
    Bool [- C -] satisfies Bool [- prop == (Bool b) -] ->
    Bool [- C -] satisfies Bool [- prop != (Bool (negb b)) -]

| C_Satisfies_AnyBool: forall C prop,
    Bool [- C -] satisfies Bool [- prop == true || prop == false -]

| C_Satisfies_AndRight: forall C1 C2 C3 t,
    t [- C1 -] satisfies t [- C2 -] ->
    t [- C1 -] satisfies t [- C3 -] ->
    t [- C1 -] satisfies t [- C2 && C3 -]
| C_Satisfies_AndLeft_Left: forall C1 C2 C3 C t,
    t [- C1 -] satisfies t [- C3 -] ->
    t [- C -] satisfies t [- C1 && C2 -] ->
    t [- C -] satisfies t [- C3 -]
| C_Satisfies_AndLeft_Right: forall C1 C2 C3 C t,
    t [- C2 -] satisfies t [- C3 -] ->
    t [- C -] satisfies t [- C1 && C2 -] ->
    t [- C -] satisfies t [- C3 -]

| C_Satisfies_OrRight_Left: forall C1 C2 C3 t,
    t [- C1 -] satisfies t [- C2 -] ->
    t [- C1 -] satisfies t [- C2 || C3 -]
| C_Satisfies_OrRight_Right: forall C1 C2 C3 t,
    t [- C1 -] satisfies t [- C3 -] ->
    t [- C1 -] satisfies t [- C2 || C3 -]
| C_Satisfies_OrLeft: forall C1 C2 C3 C t,
    t [- C1 -] satisfies t [- C3 -] ->
    t [- C2 -] satisfies t [- C3 -] ->
    t [- C -] satisfies t [- C1 || C2 -] ->
    t [- C -] satisfies t [- C3 -]

| C_Satisfies_Le_Le: forall prim1 prim2 prop C t,
    PrimLe prim1 prim2 -> 
    t [- C -] satisfies t [- prop < prim1 -] ->
    t [- C -] satisfies t [- prop < prim2 -]
| C_Satisfies_Le_Neq: forall prim1 prim2 prop C t,
    PrimLe prim1 prim2 -> 
    t [- C -] satisfies t [- prop < prim1 -] ->
    t [- C -] satisfies t [- prop != prim2 -]
| C_Satisfies_Eq_Le: forall prim1 prim2 prop C t,
    PrimLe prim1 prim2 -> 
    t [- C -] satisfies t [- prop == prim1 -] ->
    t [- C -] satisfies t [- prop < prim2 -]

| C_Satisfies_Le_LeEq: forall prim prop C t,
    IsNumberType prim -> 
    t [- C -] satisfies t [- prop < prim -] ->
    t [- C -] satisfies t [- prop <= prim -]
| C_Satisfies_Eq_LeEq: forall prim prop C t,
    IsNumberType prim ->
    t [- C -] satisfies t [- prop == prim -] -> 
    t [- C -] satisfies t [- prop <= prim -]

| C_Satisfies_LeAnd_Le_Int: forall z prop C,
    Int [- C -] satisfies Int [- prop < Int z && prop != Int (Z.sub z 1) -] ->
    Int [- C -] satisfies Int [- prop < Int (Z.sub z 1) -]

| C_Satisfies_LeEq_LeOr_Int: forall z prop C,
    Int [- C -] satisfies Int [- prop <= Int z -] ->
    Int [- C -] satisfies Int [- prop < Int z || prop == Int z -]



| C_Satisfies_Ge_Ge: forall prim1 prim2 prop C t,
    PrimGe prim1 prim2 -> 
    t [- C -] satisfies t [- prop > prim1 -] ->
    t [- C -] satisfies t [- prop > prim2 -]
| C_Satisfies_Ge_Neq: forall prim1 prim2 prop C t,
    PrimGe prim1 prim2 -> 
    t [- C -] satisfies t [- prop > prim1 -] ->
    t [- C -] satisfies t [- prop != prim2 -]
| C_Satisfies_Eq_Ge: forall prim1 prim2 prop C t,
    PrimGe prim1 prim2 -> 
    t [- C -] satisfies t [- prop == prim1 -] ->
    t [- C -] satisfies t [- prop > prim2 -]

| C_Satisfies_Ge_GeEq: forall prim prop C t,
    IsNumberType prim -> 
    t [- C -] satisfies t [- prop > prim -] ->
    t [- C -] satisfies t [- prop >= prim -]
| C_Satisfies_Eq_GeEq: forall prim prop C t,
    IsNumberType prim ->
    t [- C -] satisfies t [- prop == prim -] -> 
    t [- C -] satisfies t [- prop >= prim -]

| C_Satisfies_GeAnd_Ge_Int: forall z prop C,
    Int [- C -] satisfies Int [- prop > Int z && prop != Int (Z.add z 1) -] ->
    Int [- C -] satisfies Int [- prop > Int (Z.add z 1) -]

| C_Satisfies_GeEq_GeOr_Int: forall z prop C,
    Int [- C -] satisfies Int [- prop >= Int z -] ->
    Int [- C -] satisfies Int [- prop > Int z || prop == Int z -]

where "C1 'satisfies' C2" := (C_Satisfy_Rules C1 C2).

Lemma satisfyTypesSame :
    forall C1 C2 t1 t2,
    t1 [- C1 -] satisfies t2 [- C2 -] ->
    t1 = t2.
Proof.
    intros C1 C2 t1 t2 H.
    inversion H; subst; reflexivity.
Qed.

Ltac CorrectTypes := 
    repeat match goal with 
    | H: ?t1 [- ?C1 -] satisfies ?t2 [- ?C2 -] |- _=> 
        let eq := fresh "eq" in
        assert (t1 = t2) as eq; [apply (satisfyTypesSame C1 C2 t1 t2 H)| rewrite eq in *; clear eq ]
    | H_element : ?a elementOf ?t [- C_Constraint _ -] |- _ => 
        inversion H_element; subst; clear H_element
    | prim: R_Lang_Primitive |- _ => 
        match goal with  
        | H: IsNumberType prim |- _ => 
            destruct prim; try contradiction
        | H: PrimLe _ prim |- _ => 
            destruct prim; try contradiction
        | H: PrimLe prim _ |- _ => 
            destruct prim; try contradiction
        | H: PrimGe _ prim |- _ => 
            destruct prim; try contradiction
        | H: PrimGe prim _ |- _ => 
            destruct prim; try contradiction
        | H: baseTypeOf prim = Bool |- _ => 
            destruct prim; try discriminate
        | H: baseTypeOf prim = Int |- _ => 
            destruct prim; try discriminate
        | _ => fail
        end
    | |- ?a elementOf (baseTypeOf ?a) [- C_Constraint (_,(_,?b)) -] =>
        let H := fresh "H" in 
        assertIfNonExistentNamed (baseTypeOf (a) = baseTypeOf (b)) H;
        [logicAuto| rewrite H in *]
    end.

Ltac SatisfiesConstructor :=
    multimatch goal with 
    | |- ?t [- _ -] satisfies ?t [- _ -] => 
        apply C_Satisfies_Equal
    | |- ?t [- _ -] satisfies ?t [- Any -] => 
        apply C_Satisfies_Any
    | |- Bool [- _ -] satisfies Bool [- _ != (Bool _) -] => 
        eapply C_Satisfies_NeqBool
    | |- Bool [- _ -] satisfies Bool [- _ == true || _ == false -] =>
        eapply C_Satisfies_AnyBool

    | |- ?t [- _ -] satisfies ?t [- _ && _ -] =>
        eapply C_Satisfies_AndRight
    | |- ?t [- _ && _ -] satisfies ?t [- _ -] =>
        eapply C_Satisfies_AndLeft_Left
    | H: ?t [- ?C -] satisfies ?t [- _ && _ -]
        |- ?t [- ?C -] satisfies ?t [- _ -] =>
        eapply C_Satisfies_AndLeft_Left
    | |- ?t [- _ && _ -] satisfies ?t [- _ -] =>
        eapply C_Satisfies_AndLeft_Right
    | H: ?t [- ?C -] satisfies ?t [- _ && _ -]
        |- ?t [- ?C -] satisfies ?t [- _ -] =>
        eapply C_Satisfies_AndLeft_Right

    | |- ?t [- _ -] satisfies ?t [- _ || _ -] => 
        eapply C_Satisfies_OrRight_Left
    | |- ?t [- _ -] satisfies ?t [- _ || _ -] =>
        eapply C_Satisfies_OrRight_Right
    | |- ?t [- _ || _ -] satisfies ?t [- _ -] =>
        eapply C_Satisfies_OrLeft
        | H: ?t [- ?C -] satisfies ?t [- ?C1 || ?C2 -]
        |- ?t [- ?C -] satisfies ?t [- ?C3 -] =>
        apply (C_Satisfies_OrLeft C1 C2 C3 C t) 

    | |- ?t [- _ -] satisfies ?t [- _ < _ -] =>
        eapply C_Satisfies_Le_Le
    | |- ?t [- _ -] satisfies ?t [- _ != _ -] =>
        eapply C_Satisfies_Le_Neq
    | |- ?t [- _ -] satisfies ?t [- _ < _ -] =>
        eapply C_Satisfies_Eq_Le
    | |- ?t [- _ -] satisfies ?t [- _ <= _ -] =>
        eapply C_Satisfies_Le_LeEq
    | |- ?t [- _ -] satisfies ?t [- _ <= _ -] =>
        eapply C_Satisfies_Eq_LeEq
    | |- Int [- _ -] satisfies Int [- _ < Int (Z.sub _ 1) -] =>
        eapply C_Satisfies_LeAnd_Le_Int
    | |- Int [- _ -] satisfies Int [- ?prop < Int ?z || ?prop == Int ?z -] =>
        eapply C_Satisfies_LeEq_LeOr_Int
    
    | |- ?t [- _ -] satisfies ?t [- _ > _ -] =>
        eapply C_Satisfies_Ge_Ge
    | |- ?t [- _ -] satisfies ?t [- _ != _ -] =>
        eapply C_Satisfies_Ge_Neq
    | |- ?t [- _ -] satisfies ?t [- _ > _ -] =>
        eapply C_Satisfies_Eq_Ge
    | |- ?t [- _ -] satisfies ?t [- _ >= _ -] =>
        eapply C_Satisfies_Ge_GeEq
    | |- ?t [- _ -] satisfies ?t [- _ >= _ -] =>
        eapply C_Satisfies_Eq_GeEq
    | |- Int [- _ -] satisfies Int [- _ > Int (Z.add _ 1) -] =>
        eapply C_Satisfies_GeAnd_Ge_Int
    | |- Int [- _ -] satisfies Int [- ?prop > Int ?z || ?prop == Int ?z -] =>
        eapply C_Satisfies_GeEq_GeOr_Int
    end.


Ltac SatisfiesAuto := 
    try solve[do 5 try (
        logicAuto; (
            applyFromContext ||
            SatisfiesConstructor
        )
    )].

Lemma satisfiesAndInversion:
    forall C1 C2 C3 t,
    t [- C1 -] satisfies t [- C2 && C3 -] ->
    t [- C1 -] satisfies t [- C2 -] /\ t [- C1 -] satisfies t [- C3 -].
Proof.
    intros C1 C2 C3 t H. split; inversion H;
    subst.
    par: SatisfiesAuto.
Qed.

Theorem SatisfyTransitive:
    forall C1 C2 C3 t,
        t [- C1 -] satisfies t [- C2 -] ->
        t [- C2 -] satisfies t [- C3 -] ->
        t [- C1 -] satisfies t [- C3 -].
Proof.
    intros C1 C2 C3 t H H0;
    induction H0; try assumption.
    all: repeat match goal with
    | IH: ?A -> ?B, H: ?A |- _ => specialize (IH H)
    | H: ?t1 [- ?C1 -] satisfies ?t2 [- ?C2 -] |- _=> 
        let eq := fresh "eq" in
        assert (t1 = t2) as eq; [apply (satisfyTypesSame C1 C2 t1 t2 H)| rewrite eq in *; clear eq ]
    end.
    all: try solve[repeat (SatisfiesConstructor; unifyAssumption)].
Qed.

Ltac SatisfiesAuto ::= 
    try solve[
        repeat match goal with 
        | H: ?t1 [- ?C1 -] satisfies ?t2 [- ?C2 -] |- _=> 
            let eq := fresh "eq" in
            assert (t1 = t2) as eq; [apply (satisfyTypesSame C1 C2 t1 t2 H)| rewrite eq in *; clear eq ]
        | H: ?t [- ?C1 -] satisfies ?t [- ?C2 && ?C3 -] |- _ =>
            tryif notHypothesis (t [- C1 -] satisfies t [- C2 -]) || notHypothesis (t [- C1 -] satisfies t [- C2 -])
            then let H0 := fresh "H" in let eq := fresh "eq" in 
                remember H as H0 eqn: eq;
                clear eq;
                apply satisfiesAndInversion in H0;
                destruct H0
            else fail
        end;
        (try solve[repeat (SatisfiesConstructor; unifyAssumption)]);
        do 5 try (
            logicAuto; (
                applyFromContext ||
                SatisfiesConstructor
            )
        )
    ].



Theorem SatisfyImplicationCorrect:
    forall C1 C2 t,
        t [- C1 -] satisfies t [- C2 -] -> 
        forall a, a elementOf t [- C1 -] -> a elementOf t [- C2 -].
Proof.
    intros C1 C2 t H_sat. 
    induction H_sat; 
    intros a H_element; try assumption.

    all: repeat match goal with 
    | H: ?t [- ?C1 -] satisfies ?t [- ?C2 && ?C3 -] |- _ =>
        tryif notHypothesis (t [- C1 -] satisfies t [- C2 -]) || notHypothesis (t [- C1 -] satisfies t [- C2 -])
        then let H0 := fresh "H" in let eq := fresh "eq" in 
            remember H as H0 eqn: eq;
            clear eq;
            apply satisfiesAndInversion in H0;
            destruct H0
        else fail
    | IH: forall a, a elementOf ?t [- ?C -] -> _, H: ?a elementOf ?t [- ?C -] |- _ => 
        specialize (IH a H)
    | H: _ elementOf _ [- _ &&  _ -] |- _  => 
        inversion H; subst; clear H
    | H: _ elementOf _ [- _ ||  _ -] |- _  => 
        inversion H; subst; clear H
    end.
    all: CorrectTypes.

    all: repeat match goal with 
    | b: bool |-  _ => destruct b
    | p: C_Lang_Property |- _ => destruct p
    end.
    
    all: try solve[repeat (ElementOfContstuctor; logicAuto)].

    all: try solve [repeat (logicAuto; applyFromContext)].

    - assert (baseTypeOf a = Bool); [ eapply typingMatters; unifyAssumption|].
        destruct a; try discriminate.
        destruct b; try solve[repeat (ElementOfContstuctor; logicAuto)].

    - logicAuto. 
        eapply C_ElementOf_Le; try (reflexivity).
        unfold PrimLe in *.
        admit. (* linear integer arithemtic *)
    - logicAuto. 
        eapply C_ElementOf_NotEqual; try reflexivity. 
        unfold PrimLe in *.
        admit. (* linear integer arithemtic *)
    - logicAuto. 
        apply C_ElementOf_Le; try reflexivity.
        unfold PrimLe in *.
        admit. (* linear integer arithemtic *)
    - assert (baseTypeOf a = Int); [ eapply typingMatters; unifyAssumption|]. 
        logicAuto; try solve[repeat (ElementOfContstuctor; logicAuto)].


    - logicAuto. 
        eapply C_ElementOf_Ge; try (reflexivity).
        unfold PrimGe in *.
        admit. (* linear integer arithemtic *)
    - logicAuto. 
        eapply C_ElementOf_NotEqual; try reflexivity. 
        unfold PrimGe in *.
        admit. (* linear integer arithemtic *)
    - logicAuto. 
        apply C_ElementOf_Ge; try reflexivity.
        unfold PrimGe in *.
        admit. (* linear integer arithemtic *)
    - assert (baseTypeOf a = Int); [ eapply typingMatters; unifyAssumption|]. 
        logicAuto; try solve[repeat (ElementOfContstuctor; logicAuto)].  
Admitted.


Theorem SatisfyComplete:
    forall t C1 C2,
        nonEmpty t [- C1 -] ->
        (forall a, a elementOf t [- C1 -] -> a elementOf t [- C2 -]) -> 
        t [- C1 -] satisfies t [- C2 -].
Proof.
    intros t C1 C2 H_nonEmpty H_sat.
    destruct H_nonEmpty as [elem H_nonEmpty1].
    (* remember H_nonEmpty1 as H_nonEmpty2 eqn: eq;
    clear eq; apply H_sat in H_nonEmpty2. *)
    induction H_nonEmpty1.
    try solve[repeat (SatisfiesConstructor; unifyAssumption)].

Admitted.

