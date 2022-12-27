Require Import definitions.

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

Definition simpleConstraint := (C_Lang_Property * (C_Lang_Operator * R_Lang_Primitive))%type.

(* this is the core of the constraints language
    a type can either have no constraint or a single constraint *)
Inductive Constraints_Lang: Type :=
| C_NoConstraint: Constraints_Lang
| C_Constraint: simpleConstraint -> Constraints_Lang
.


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


Reserved Notation " '[-' c1 '-]' 'satisfies' '[-' c2 '-]'".
Inductive C_Satisfy_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=
| C_Satisfy_NoConstraint: forall constraint,
    [- constraint -] satisfies [- C_NoConstraint -]

| C_Satisfy_SimpleConstriants: forall simple1 simple2,
    simpleSatisfies simple1 simple2 = true ->
    [- C_Constraint simple1 -] satisfies [-C_Constraint simple2-]

where  " '[-' c1 '-]' 'satisfies' '[-' c2 '-]'" := (C_Satisfy_Rules c1 c2).




(* proof that the inductive version of satisfy is equivalent to the 
    computational version *)
Theorem satisfyEquivalent:
    forall constraint constraint',
    ([-constraint-] satisfies [-constraint'-]) <-> (satisfy constraint constraint' = true) .
Proof.
    induction constraint; induction constraint'; split; intros;
        repeat (match goal with 
        | |- [-_ -] satisfies [-C_NoConstraint -] => apply C_Satisfy_NoConstraint
        | H: simpleSatisfies ?c ?c' = true |- 
            [-C_Constraint ?c -] satisfies [-C_Constraint ?c' -] => 
            apply C_Satisfy_SimpleConstriants; assumption
        | |- satisfy _ _ = true => simpl
        | H: [- _ -] satisfies [- _ -] |- _ => inversion H; subst; clear H
        | H: satisfy _ _ = _ |- _=> simpl in H
        end; try (reflexivity || discriminate || assumption)).    
Qed.


