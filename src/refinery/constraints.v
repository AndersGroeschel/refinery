Require Import definitions.


Inductive C_Lang_Property : Type := 
    | C_Prop_Self: C_Lang_Property
.

Definition propertiesSame prop1 prop2 := 
match (prop1, prop2) with 
    | (C_Prop_Self,C_Prop_Self) => true
end.

Inductive C_Lang_Operator: Type :=
| C_Op_Equal
| C_Op_NotEqual
.

Definition negateOp op :=
    match op with 
    | C_Op_Equal => C_Op_NotEqual
    | C_Op_NotEqual => C_Op_Equal
    end.

Definition simpleConstraint := (C_Lang_Property * (C_Lang_Operator * R_Lang_Primitive))%type.


Inductive Constraints_Lang: Type :=
| C_NoConstraint: Constraints_Lang
| C_Constraint: simpleConstraint -> Constraints_Lang
.



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
