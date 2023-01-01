Require Import definitions.
Require Import Bool.
Require Import ZArith.

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

Notation " '[-' x '-]' " := (x : Constraints_Lang) (at level 0, x custom constraint at level 99).
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
Notation " 'bool' b " :=  (R_Prim_Bool b) (in custom constraint at level 0, no associativity).
Notation " 'int' z " :=  (R_Prim_Int z) (in custom constraint at level 0, no associativity).

Notation "x && y"  := (C_And x y) (in custom constraint at level 80, left associativity).
Notation "x || y"  := (C_Or x y) (in custom constraint at level 80, left associativity).

Notation " prop '==' prim " := (C_Constraint (prop, (C_Op_Equal, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '!=' prim " := (C_Constraint (prop, (C_Op_NotEqual, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '<' prim " := (C_Constraint (prop, (C_Op_LessThan, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '>' prim " := (C_Constraint (prop, (C_Op_GreaterThan, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '<=' prim " := (C_Constraint (prop, (C_Op_LessThanEqual, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '>=' prim " := (C_Constraint (prop, (C_Op_GreaterThanEqual, prim))) (in custom constraint at level 70, no associativity).

Ltac solveWithConstructor C := 
    solve [
        eapply C;
        match goal with 
        | H: ?P |- ?P' => unify P P'; apply H
        end
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

Ltac specializeHypothesis :=
    match goal with 
    | H: ?P, IH: ?P -> _ |- _ => specialize (IH H)
    end.



Reserved Notation "c1 'equivalentTo' c2" (at level 40).
Inductive C_Equivalent_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=
| C_Equivalent_Exact: forall C, 
    C equivalentTo C

| C_Equivalent_Transitive: forall C C' C'',
    C equivalentTo C' ->
    C' equivalentTo C'' ->
    C equivalentTo C''

| C_Equivalent_AndComm: forall C C',
    [- C && C' -] equivalentTo [- C' && C -]

| C_Equivalent_AndStep: forall C C' C'',
    C equivalentTo C'' ->
    [- C && C' -] equivalentTo [- C'' && C' -]
| C_Equivalent_AndAssoc1: forall C C' C'',
    [- C && (C' && C'') -] equivalentTo [- (C && C') && C'' -]
| C_Equivalent_AndAssoc2: forall C C' C'',
    [- (C && C') && C'' -] equivalentTo [- C && (C' && C'') -]
| C_Equivalent_AndSame1: forall C,
    C equivalentTo [- C && C-]
| C_Equivalent_AndSame2: forall C,
    [- C && C-] equivalentTo C

| C_Equivalent_AndNoConstraint1: forall C,
    [- C && Any -] equivalentTo [- C -]
| C_Equivalent_AndNoConstraint2: forall C,
    [- C -] equivalentTo [- C && Any -]

| C_Equivalent_OrComm: forall C C',
    [- C || C' -] equivalentTo [- C' || C -]
| C_Equivalent_OrStep: forall C C' C'',
    C equivalentTo C'' ->
    [- C || C' -] equivalentTo [- C'' || C' -]
| C_Equivalent_OrAssoc1: forall C C' C'',
    [- C || (C' || C'') -] equivalentTo [- (C || C') || C'' -]
| C_Equivalent_OrAssoc2: forall C C' C'',
    [- (C || C') || C'' -] equivalentTo [- C || (C' || C'') -]
| C_Equivalent_OrSame1: forall C,
    C equivalentTo [- C || C -]
| C_Equivalent_OrSame2: forall C,
    [- C || C -] equivalentTo C

| C_Equivalent_OrNoConstraint1: forall C,
    [- C || Any -] equivalentTo [- Any -]
| C_Equivalent_OrNoConstraint2: forall C,
    [- Any -] equivalentTo [- C || Any -]



| C_Equivalent_BoolNeq1: forall prop b,
    [- prop == (bool b) -] equivalentTo [- prop != (bool (negb b)) -]
| C_Equivalent_BoolNeq2: forall prop b,
    [- prop != (bool (negb b)) -] equivalentTo [- prop == (bool b) -]

| C_Equivalent_BoolOr1: forall prop,
    [- prop == true || prop == false -] equivalentTo [- Any -]
| C_Equivalent_BoolOr2: forall prop,
    [- Any -] equivalentTo [- prop == true || prop == false -]

| C_Equivalent_LeInt1: forall prop z,
    [- prop < int z -] equivalentTo [- prop < int (Z.add z 1) && prop != int (Z.add z 1)  -]
| C_Equivalent_LeInt2: forall prop z,
    [- prop < int (Z.add z 1) && prop != int (Z.add z 1)  -] equivalentTo [- prop < int z -]
| C_Equivalent_LeInt3: forall prop z,
    [- prop < int z -] equivalentTo [- prop < int (Z.sub z 1) || prop == int (Z.sub z 1) -]
| C_Equivalent_LeInt4: forall prop z,
    [- prop < int (Z.sub z 1) || prop == int (Z.sub z 1) -] equivalentTo [- prop < int z -]
| C_Equivalent_LeInt5: forall prop z,
    [- prop < int z -] equivalentTo [- prop <= int (Z.sub z 1) -]
| C_Equivalent_LeInt6: forall prop z,
    [- prop <= int (Z.sub z 1) -] equivalentTo [- prop < int z -]

| C_Equivalent_GeInt1: forall prop z,
    [- prop > int z -] equivalentTo [- prop > int (Z.sub z 1) && prop != int (Z.sub z 1)  -]
| C_Equivalent_GeInt2: forall prop z,
    [- prop > int (Z.sub z 1) && prop != int (Z.sub z 1)  -] equivalentTo [- prop > int z -]
| C_Equivalent_GeInt3: forall prop z,
    [- prop > int z -] equivalentTo [- prop > int (Z.add z 1) || prop == int (Z.add z 1) -]
| C_Equivalent_GeInt4: forall prop z,
    [- prop > int (Z.add z 1) || prop == int (Z.add z 1) -] equivalentTo [- prop > int z -]
| C_Equivalent_GeInt5: forall prop z,
    [- prop > int z -] equivalentTo [- prop >= int (Z.add z 1) -]
| C_Equivalent_GeInt6: forall prop z,
    [- prop >= int (Z.add z 1) -] equivalentTo [- prop > int z -]


| C_Equivalent_NeqInt1: forall prop z,
    [- prop != int z -] equivalentTo [- prop > int z || prop < int z -]
| C_Equivalent_NeqInt2: forall prop z,
    [- prop > int z || prop < int z -] equivalentTo [- prop != int z -]

| C_Equivalent_EqInt1: forall prop z,
    [- prop == int z -] equivalentTo [- prop >= int z && prop <= int z -]
| C_Equivalent_EqInt2: forall prop z,
    [- prop >= int z && prop <= int z -] equivalentTo [- prop == int z -]

where "c1 'equivalentTo' c2" := (C_Equivalent_Rules c1 c2).

Ltac equivalenceConstructor :=
match goal with 
| |- _ equivalentTo _ =>
    (solveWithConstructor C_Equivalent_Exact) ||
    (solveWithConstructor C_Equivalent_Transitive) ||
    (solveWithConstructor C_Equivalent_AndComm) ||
    (solveWithConstructor C_Equivalent_AndStep) ||
    (solveWithConstructor C_Equivalent_AndAssoc1) ||
    (solveWithConstructor C_Equivalent_AndAssoc2) ||
    (solveWithConstructor C_Equivalent_AndSame1) ||
    (solveWithConstructor C_Equivalent_AndSame2) ||
    (solveWithConstructor C_Equivalent_AndNoConstraint1) ||
    (solveWithConstructor C_Equivalent_AndNoConstraint2) ||
    (solveWithConstructor C_Equivalent_OrComm) ||
    (solveWithConstructor C_Equivalent_OrStep) ||
    (solveWithConstructor C_Equivalent_OrAssoc1) ||
    (solveWithConstructor C_Equivalent_OrAssoc2) ||
    (solveWithConstructor C_Equivalent_OrSame1) ||
    (solveWithConstructor C_Equivalent_OrSame2) ||
    (solveWithConstructor C_Equivalent_OrNoConstraint1) ||
    (solveWithConstructor C_Equivalent_OrNoConstraint2) ||
    (solveWithConstructor C_Equivalent_BoolNeq1) ||
    (solveWithConstructor C_Equivalent_BoolNeq2) ||
    (solveWithConstructor C_Equivalent_BoolOr1) ||
    (solveWithConstructor C_Equivalent_BoolOr2) ||
    (solveWithConstructor C_Equivalent_LeInt1) ||
    (solveWithConstructor C_Equivalent_LeInt2) ||
    (solveWithConstructor C_Equivalent_LeInt3) ||
    (solveWithConstructor C_Equivalent_LeInt4) ||
    (solveWithConstructor C_Equivalent_LeInt5) ||
    (solveWithConstructor C_Equivalent_LeInt6) ||
    (solveWithConstructor C_Equivalent_GeInt1) ||
    (solveWithConstructor C_Equivalent_GeInt2) ||
    (solveWithConstructor C_Equivalent_GeInt3) ||
    (solveWithConstructor C_Equivalent_GeInt4) ||
    (solveWithConstructor C_Equivalent_GeInt5) ||
    (solveWithConstructor C_Equivalent_GeInt6) ||
    (solveWithConstructor C_Equivalent_NeqInt1) ||
    (solveWithConstructor C_Equivalent_NeqInt2) ||
    (solveWithConstructor C_Equivalent_EqInt1) || 
    (solveWithConstructor C_Equivalent_EqInt2)
end.

Theorem equivalenceCommutative:
    forall C C',
    C equivalentTo C' -> C' equivalentTo C.
Proof.
    intros C C' H.
    induction H; subst;
    try equivalenceConstructor.
Qed.

Reserved Notation "c1 'excludes' c2" (at level 40).
Inductive C_Exlusion_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=

| C_Excludes_ConstraintEquivalence: forall C C' Ce Ce',
    C equivalentTo Ce ->
    C' equivalentTo Ce' ->
    Ce excludes Ce' ->
    C excludes C'

| C_Excludes_AndRight_Left: forall C C' C'',
    C excludes C' ->
    C excludes [- C' && C'' -]
| C_Excludes_AndRight_Right: forall C C' C'',
    C excludes C'' ->
    C excludes [- C' && C'' -]

| C_Excludes_AndLeft_Left: forall C C' C'',
    C excludes C'' ->
    [- C && C' -] excludes C''
| C_Excludes_AndLeft_Right: forall C C' C'',
    C' excludes C'' ->
    [- C && C' -] excludes C''

| C_Excludes_OrRight: forall C C' C'',
    C excludes C' -> 
    C excludes C'' ->
    C excludes [- C' || C'' -]
| C_Excludes_OrLeft: forall C C' C'',
    C excludes C'' -> 
    C' excludes C'' ->
    [- C || C' -] excludes C''


| C_Exludes_Eq_Neq: forall prop prim,
    [- prop == prim -] excludes [- prop != prim-]

| C_Exludes_Neq_Eq: forall prop prim,
    [- prop != prim -] excludes [- prop == prim-]

| C_Exludes_EqDiff: forall prop prim prim',
    prim <> prim' ->
    [- prop == prim -] excludes [- prop == prim'-]

| C_Excludes_LeGe: forall prop z z',
    z < z' ->
    [- prop <= int z -] excludes [- prop >= int z' -]
| C_Excludes_GeLe: forall prop z z',
    z > z' ->
    [- prop >= int z -] excludes [- prop <= int z' -]

| C_Excludes_LeEq: forall prop z z',
    z < z' ->
    [- prop <= int z -] excludes [- prop == int z' -]

| C_Excludes_EqLe: forall prop z z',
    z > z' ->
    [- prop == int z -] excludes [- prop <= int z' -]

| C_Excludes_GeEq: forall prop z z',
    z > z' ->
    [- prop >= int z -] excludes [- prop == int z' -]

| C_Excludes_EqGe: forall prop z z',
    z < z' ->
    [- prop == int z -] excludes [- prop >= int z' -]

where "c1 'excludes' c2" := (C_Exlusion_Rules c1 c2).

Ltac exclusionConstructors := 
match goal with 
| |- _ excludes _ =>
    (solveWithConstructor C_Exludes_Eq_Neq) ||
    (solveWithConstructor C_Exludes_Neq_Eq) ||
    (solveWithConstructor C_Exludes_EqDiff) ||
    (solveWithConstructor C_Excludes_LeGe) ||
    (solveWithConstructor C_Excludes_GeLe) ||
    (solveWithConstructor C_Excludes_LeEq) ||
    (solveWithConstructor C_Excludes_EqLe) ||
    (solveWithConstructor C_Excludes_GeEq) ||
    (solveWithConstructor C_Excludes_EqGe) ||
    (solveWithConstructor C_Excludes_ConstraintEquivalence) ||
    (solveWithConstructor C_Excludes_AndRight_Right) ||
    (solveWithConstructor C_Excludes_AndLeft_Right) ||
    (solveWithConstructor C_Excludes_AndRight_Left) ||
    (solveWithConstructor C_Excludes_AndLeft_Left) ||
    (solveWithConstructor C_Excludes_OrRight) ||
    (solveWithConstructor C_Excludes_OrLeft)
end.



Theorem exclusionCommutative: 
    forall C C',
    C excludes C' ->
    C' excludes C. 
Proof.
    intros C C' H.
    induction H; subst;
    try flipRelations;
    try exclusionConstructors.
Qed.


Reserved Notation "c1 'satisfies' c2" (at level 40).
Inductive C_Satisfy_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=
| C_Satisfy_NoConstraint: forall C C',
    C' equivalentTo [- Any -] ->
    C satisfies C'

| C_Satisfy_Equivalence: forall C C',
    C equivalentTo C' ->
    C satisfies C'

| C_Satisfy_ConstraintEquivalence: forall C C' Cs Cs',
    C equivalentTo Cs ->
    C' equivalentTo Cs' ->
    Cs satisfies Cs' ->
    C satisfies C'


| C_Satisfy_AndRight: forall C C' C'',
    C satisfies C' ->
    C satisfies C'' ->
    C satisfies [- C' && C'' -]
| C_Satisfy_AndLeft_Left: forall C C' C'',
    C satisfies C'' ->
    [- C && C' -] satisfies C''
| C_Satisfy_AndLeft_Right: forall C C' C'',
    C' satisfies C'' ->
    [- C && C' -] satisfies C''


| C_Satisfy_OrRight_Left: forall C C' C'',
    (C satisfies C') ->
    C satisfies [- C' || C'' -]
| C_Satisfy_OrRight_Right: forall C C' C'',
    (C satisfies C'') ->
    C satisfies [- C' || C'' -]
| C_Satisfy_OrLeft: forall C C' C'',
    C satisfies C'' ->
    C' satisfies C'' ->
    [- C || C' -] satisfies C''


| C_Satisfy_LeEqLeEq: forall z z' prop, 
    z <= z' ->
    [- prop <= int z -] satisfies [- prop <= int z' -]

| C_Satisfy_GeEqGeEq: forall z z' prop, 
    z >= z' ->
    [- prop >= int z -] satisfies [- prop >= int z' -]

where  " c1 'satisfies' c2 " := (C_Satisfy_Rules c1 c2).

Ltac satisfiesConstructors := 
match goal with 
| |- _ satisfies _ =>
    (solveWithConstructor C_Satisfy_NoConstraint) ||
    (solveWithConstructor C_Satisfy_Equivalence) ||
    (solveWithConstructor C_Satisfy_ConstraintEquivalence) ||
    (solveWithConstructor C_Satisfy_AndRight) ||
    (solveWithConstructor C_Satisfy_AndLeft_Left) ||
    (solveWithConstructor C_Satisfy_AndLeft_Right) ||
    (solveWithConstructor C_Satisfy_OrRight_Left) ||
    (solveWithConstructor C_Satisfy_OrRight_Right) ||
    (solveWithConstructor C_Satisfy_OrLeft) ||
    (solveWithConstructor C_Satisfy_LeEqLeEq) ||
    (solveWithConstructor C_Satisfy_GeEqGeEq)
end.

Theorem satisfiesAnd:
    forall C C' C'',
    C satisfies [- C' && C'' -] ->
    C satisfies C' /\ C satisfies C''.
Proof.
    Admitted.

Theorem satisfiesOr:
    forall C C' C'',
    C satisfies [- C' || C'' -] ->
    C satisfies C' \/ C satisfies C''.
Proof.
    Admitted.




Theorem ExludeNotSatisfy:
    forall C C',
    C excludes C' ->
    ~ (C satisfies C').
Proof.
    intros C C' H contra;
    induction H; subst;
    try match goal with
    | Equiv1: ?C equivalentTo ?Ce,
        Equiv2: ?C' equivalentTo ?Ce',
        H: ?C satisfies ?C' |- _ => 
        notHypothesis (Ce satisfies Ce');
        apply equivalenceCommutative in Equiv1;
        apply equivalenceCommutative in Equiv2;
        let new := fresh "H" in
        (assert (Ce satisfies Ce') as new; 
        try solveWithConstructor C_Satisfy_ConstraintEquivalence);
        apply equivalenceCommutative in Equiv1;
        apply equivalenceCommutative in Equiv2
    end;
    try specializeHypothesis;
    try contradiction.
    Admitted.
    

Theorem SatisfyNotExlude:
    forall C C',
    C satisfies C' ->
    ~ (C excludes C').
Proof.
    Admitted.


(* correctness Theorems *)
Theorem EquivNotExlude:
    forall C C',
    C equivalentTo C' ->
    ~ (C excludes C').
Proof.
    Admitted.

Theorem ExludeNotEquive:
    forall C C',
    C excludes C' ->
    ~ (C equivalentTo C').
Proof.
    Admitted.

Theorem EquivSatisfaction:
    forall C C',
    C equivalentTo C' <-> (C satisfies C' /\ C' satisfies C).
Proof.
    Admitted.
