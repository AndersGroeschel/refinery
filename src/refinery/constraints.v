Require Import definitions.
Require Import Bool.

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
.

(* take a relationship and do the oposite*)
Definition negateOp op :=
    match op with 
    | C_Op_Equal => C_Op_NotEqual
    | C_Op_NotEqual => C_Op_Equal
    end.

Definition cOpsEqual op1 op2 := 
    match (op1, op2) with 
    | (C_Op_Equal,C_Op_Equal) => true
    | (C_Op_NotEqual,C_Op_NotEqual) => true
    | _ => false
    end.

Definition simpleConstraint := (C_Lang_Property * (C_Lang_Operator * R_Lang_Primitive))%type.

(* this is the core of the constraints language
    a type can either have no constraint or a single constraint *)
Inductive Constraints_Lang: Type :=
| C_NoConstraint: Constraints_Lang
| C_Constraint: simpleConstraint -> Constraints_Lang
.

Notation " '[-' '-]' " := C_NoConstraint.
Notation " '[-' x '-]' " := (x: Constraints_Lang).
Notation " 'self' " := C_Prop_Self.

Notation " prop '==' prim " := (C_Constraint (prop, (C_Op_Equal, prim))) (at level 40).
Notation " prop '!=' prim " := (C_Constraint (prop, (C_Op_NotEqual, prim))) (at level 40).

Reserved Notation "c1 'equivalentTo' c2" (at level 40).
Inductive C_Equivalent_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=
| C_Equivalent_Exact: forall C, 
    C equivalentTo C

| C_Equivalent_Bool1: forall prop b,
    [- prop == (R_Prim_Bool b) -] equivalentTo [- prop != (R_Prim_Bool (negb b)) -]
| C_Equivalent_Bool2: forall prop b,
    [- prop != (R_Prim_Bool b) -] equivalentTo [- prop == (R_Prim_Bool (negb b)) -]

where "c1 'equivalentTo' c2" := (C_Equivalent_Rules c1 c2).

Definition constraintsEqual c1 c2 := 
    match (c1, c2) with 
    | (C_NoConstraint,C_NoConstraint) => true
    | (_, C_NoConstraint) => false 
    | (C_NoConstraint,_) => false 
    | (C_Constraint (prop1, (C_Op_Equal, R_Prim_Bool b1)), C_Constraint (prop2, (C_Op_NotEqual, R_Prim_Bool b2))) =>
        if propertiesSame prop1 prop2 then 
            if b1 then negb b2 else b2
        else false
    | (C_Constraint (prop1, (C_Op_NotEqual, R_Prim_Bool b1)), C_Constraint (prop2, (C_Op_Equal, R_Prim_Bool b2))) =>
        if propertiesSame prop1 prop2 then 
            if b1 then negb b2 else b2
        else false
    | (C_Constraint (prop1,(op1,prim1)), C_Constraint (prop2,(op2,prim2))) =>
        (propertiesSame prop1 prop2) && (cOpsEqual op1 op2) &&  (primitivesSame prim1 prim2) 
    end.

Theorem constraintEqualEquivalence:
    forall c c',
    (c equivalentTo c') <-> (constraintsEqual c c' = true) .
Proof.
    induction c; induction c'; split; intros;
    repeat (
        (try reflexivity || assumption || discriminate);
        match goal with 
        | |- ?c equivalentTo ?c => apply C_Equivalent_Exact
        | |- constraintsEqual _ _ => simpl
        | H: _ equivalentTo _ |- _ => inversion H; subst; clear H
        | constraint: simpleConstraint |- _ => 
            let prop := fresh "prop" in 
            let tmp := fresh "tmp" in 
            let op := fresh "op" in 
            let prim := fresh "prim" in 
            destruct constraint as [prop tmp];
            destruct tmp as [op prim]
        | b: bool |- _=> destruct b
        | prop: C_Lang_Property |- _ => destruct prop
        | op: C_Lang_Operator |- _ => destruct op
        | prim: R_Lang_Primitive |- _ => destruct prim
        | |- [- ?prop == (R_Prim_Bool true) -] equivalentTo [- ?prop != (R_Prim_Bool false) -] => apply C_Equivalent_Bool1
        | |- [- ?prop == (R_Prim_Bool false) -] equivalentTo [- ?prop != (R_Prim_Bool true) -] => apply C_Equivalent_Bool1
        | |- [- ?prop != (R_Prim_Bool true) -] equivalentTo [- ?prop == (R_Prim_Bool false) -] => apply C_Equivalent_Bool2
        | |- [- ?prop != (R_Prim_Bool false) -] equivalentTo [- ?prop == (R_Prim_Bool true) -] => apply C_Equivalent_Bool2
        end
    ).
Qed.

Reserved Notation "c1 'excludes' c2" (at level 40).
Inductive C_Exlusion_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=

| C_Exludes_Eq_Neq: forall C C' prop prim,
    C equivalentTo [- prop == prim -] ->
    C' equivalentTo [- prop != prim-] ->
    C excludes C'

| C_Exludes_Neq_Eq: forall C C' prop prim,
    C equivalentTo [- prop != prim -] ->
    C' equivalentTo [- prop == prim-] ->
    C excludes C'

| C_Exludes_EqDiff: forall C C' prop prim prim',
    prim <> prim'
    C equivalentTo [- prop == prim -] ->
    C' equivalentTo [- prop == prim'-] ->
    C excludes C'

where "c1 'excludes' c2" := (C_Exlusion_Rules c1 c2).



(* a function that says whether or not a simple constraint is 
    satisfactory for the other to be true, in other words if simple1 implies simple2 *)
Definition simpleSatisfies (simple1 simple2: simpleConstraint)  :=
    let (prop1, tmp) := simple1 in 
    let (op1, prim1) := tmp in 
    let (prop2, tmp) := simple2 in 
    let (op2, prim2) := tmp in 

    if propertiesSame prop1 prop2
    then match (op1,op2) with 
        | (C_Op_Equal,C_Op_Equal) => 
            if primitivesSame prim1 prim2
            then true
            else false
        | (C_Op_NotEqual,C_Op_Equal) => false
        | (C_Op_Equal,C_Op_NotEqual) => 
            if primitivesSame prim1 prim2
            then false
            else true
        | (C_Op_NotEqual,C_Op_NotEqual) => 
            if primitivesSame prim1 prim2
            then true
            else false
        end
    else true
.
(* does c1 satisfy the constraints of c2*)
Definition satisfy c1 c2 := 
    match c2 with 
    | C_NoConstraint => true
    | C_Constraint simple2 => match c1 with 
        | C_NoConstraint => false
        | C_Constraint simple1 => (simpleSatisfies simple1 simple2)
        end
    end.


Reserved Notation "c1 'satisfies' c2" (at level 40).
Inductive C_Satisfy_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=
| C_Satisfy_NoConstraint: forall constraint,
    constraint satisfies [- -]

| C_Satisfy_SimpleConstriants: forall simple1 simple2,
    simpleSatisfies simple1 simple2 = true ->
    [- C_Constraint simple1 -] satisfies [- C_Constraint simple2 -]

where  " c1 'satisfies' c2 " := (C_Satisfy_Rules c1 c2).




(* proof that the inductive version of satisfy is equivalent to the 
    computational version *)
Theorem satisfyEquivalence:
    forall constraint constraint',
    ( [-constraint-] satisfies [-constraint'-]) <-> (satisfy constraint constraint' = true) .
Proof.
    induction constraint; induction constraint'; split; intros;
        repeat (match goal with 
        | |- satisfy _ _ = true => simpl
        | |- _ satisfies [- -] => apply C_Satisfy_NoConstraint
        | H: _ satisfies _ |- _ => inversion H; subst; clear H
        | H: satisfy _ _ = _ |- _=> simpl in H
        | H: simpleSatisfies ?c ?c' = true |- 
            (C_Constraint ?c) satisfies (C_Constraint ?c') => 
            apply C_Satisfy_SimpleConstriants; assumption
        end; try (reflexivity || discriminate || assumption)).
Qed.


