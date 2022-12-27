Require Import definitions.
Require Import constraints.

(* the base types of the type system*)
Inductive Refinery_BaseType: Type :=
    | R_T_Bool: Refinery_BaseType
.
(* gives the base type of a primitive value *)
Definition typeOf prim :=
    match prim with 
    | R_Prim_Bool _ => R_T_Bool
    end.

Definition Refinery_RefinementType := (Refinery_BaseType * Constraints_Lang)%type.

(* the following 3 things define how a uniary operator 
transform a refinement type*)

(* given an input base type what base type is output*)
Definition uniOpTransformBaseType op base :=
    match (op,base) with 
    | (R_Not,R_T_Bool) => Some R_T_Bool
    end.

(* what constraint does the operator enforce on the input *)
Definition uniOpInputConstraint op base := 
    match (op,base) with 
    | (R_Not,R_T_Bool) => Some (C_NoConstraint)
    end
.

(* This inductive defines how a uniary operator takes a type to a type *)
Reserved Notation "op 'maps' typ1 'to' typ2" (at level 40).

Inductive R_Type_UniOp_Rule: R_Lang_UniOp -> Refinery_RefinementType -> Refinery_RefinementType -> Prop :=

| R_T_UniOp_Not_NoConstraint: 
    R_Not maps (R_T_Bool,C_NoConstraint) to (R_T_Bool,C_NoConstraint)

| R_T_UniOp_Constraint_SameOp: forall op baseIn inputConstraint c_Op prim1 prim2 baseOut,
    uniOpInputConstraint op baseIn = Some inputConstraint ->
    [- C_Constraint (C_Prop_Self, (c_Op, prim1) )-] satisfies [-inputConstraint-] -> 
    uniOpTransformsPrim op prim1 = Some prim2 -> 
    uniOpTransformBaseType op baseIn = Some baseOut ->

    op maps (baseIn, C_Constraint (C_Prop_Self, (c_Op, prim1)))
    to (baseOut,C_Constraint (C_Prop_Self, (c_Op, prim2)))

where "op 'maps' typ1 'to' typ2" := (R_Type_UniOp_Rule op typ1 typ2).


(* the following 3 things define how a binary operator 
transform a refinement type*)


(* given an input base type what base type is output*)
Definition binOpTransformBaseType op base1 base2 :=
    match (op,base1,base2) with 
    | (R_And,R_T_Bool,R_T_Bool) => Some R_T_Bool
    | (R_Or,R_T_Bool,R_T_Bool) => Some R_T_Bool
    | (R_Equal,_,_) => Some R_T_Bool
    end.

(* what constraint does the operator enforce on the input *)
Definition binOpInputConstraint op base1 base2 :=
    match (op,base1,base2) with 
    | (R_And,R_T_Bool,R_T_Bool) => Some (C_NoConstraint, C_NoConstraint)
    | (R_Or,R_T_Bool,R_T_Bool) => Some (C_NoConstraint, C_NoConstraint)
    | (R_Equal,_,_) => Some (C_NoConstraint, C_NoConstraint)
    end.

(* This inductive defines how a uniary operator takes a type to a type *)
Reserved Notation "op 'maps' typ1 'and' typ2 'to' typ3" (at level 40).

Inductive R_Type_BinOp_Rule: R_Lang_BinOp -> Refinery_RefinementType -> Refinery_RefinementType -> Refinery_RefinementType -> Prop :=

| R_T_BinOp_And_NoConstraint: 
    R_And maps (R_T_Bool,C_NoConstraint) and (R_T_Bool,C_NoConstraint) to (R_T_Bool,C_NoConstraint)

| R_T_BinOp_Or_NoConstraint: 
    R_Or maps (R_T_Bool,C_NoConstraint) and (R_T_Bool,C_NoConstraint) to (R_T_Bool,C_NoConstraint)

| R_T_BinOp_Equal_NoConstraint: forall typ1 typ2,
    R_Equal maps (typ1,C_NoConstraint) and (typ2,C_NoConstraint) to (R_T_Bool,C_NoConstraint)


| R_T_BinOp_Constraint_SameOp: forall op base1 base2 inputConstraint1 inputConstraint2 c_Op prim1 prim2 prim3 baseOut,
    binOpInputConstraint op base1 base2 = Some (inputConstraint1, inputConstraint2) ->
    [- C_Constraint (C_Prop_Self, (c_Op, prim1) )-] satisfies [-inputConstraint1-] -> 
    [- C_Constraint (C_Prop_Self, (c_Op, prim2) )-] satisfies [-inputConstraint2-] -> 

    binOpTransformsPrim op prim1 prim2 = Some prim3 -> 
    binOpTransformBaseType op base1 base2 = Some baseOut ->

    op maps (base1, C_Constraint (C_Prop_Self, (c_Op, prim1) )) 
        and (base2, C_Constraint (C_Prop_Self, (c_Op, prim2) ))
        to (baseOut,C_Constraint (C_Prop_Self, (c_Op, prim3)))


| R_T_BinOp_Constraint_Equal_NotEqual: forall op base1 base2 inputConstraint1 inputConstraint2 prim1 prim2 prim3 baseOut,
    binOpInputConstraint op base1 base2 = Some (inputConstraint1, inputConstraint2) ->
    [- C_Constraint (C_Prop_Self, (C_Op_Equal, prim1) )-] satisfies [-inputConstraint1-] -> 
    [- C_Constraint (C_Prop_Self, (C_Op_NotEqual, prim2) )-] satisfies [-inputConstraint2-] -> 

    binOpTransformsPrim op prim1 prim2 = Some prim3 -> 
    binOpTransformBaseType op base1 base2 = Some baseOut ->

    op maps (base1, C_Constraint (C_Prop_Self, (C_Op_Equal, prim1) )) 
        and (base2, C_Constraint (C_Prop_Self, (C_Op_NotEqual, prim2) ))
        to (baseOut,C_Constraint (C_Prop_Self, (C_Op_NotEqual, prim3)))

| R_T_BinOp_Constraint_NotEqual_Equal: forall op base1 base2 inputConstraint1 inputConstraint2 prim1 prim2 prim3 baseOut,
    binOpInputConstraint op base1 base2 = Some (inputConstraint1, inputConstraint2) ->
    [- C_Constraint (C_Prop_Self, (C_Op_NotEqual, prim1) )-] satisfies [-inputConstraint1-] -> 
    [- C_Constraint (C_Prop_Self, (C_Op_Equal, prim2) )-] satisfies [-inputConstraint2-] -> 

    binOpTransformsPrim op prim1 prim2 = Some prim3 -> 
    binOpTransformBaseType op base1 base2 = Some baseOut ->

    op maps (base1, C_Constraint (C_Prop_Self, (C_Op_NotEqual, prim1) )) 
        and (base2, C_Constraint (C_Prop_Self, (C_Op_Equal, prim2)))
        to (baseOut,C_Constraint (C_Prop_Self, (C_Op_NotEqual, prim3)))



where "op 'maps' typ1 'and' typ2 'to' typ3" := (R_Type_BinOp_Rule op typ1 typ2 typ3).







(* this inductive defines what type an expression has *)
Reserved Notation "exp 'hasRefinement' T" (at level 40).
Inductive Refinery_Type_Rule : Refinery_Lang -> Refinery_RefinementType -> Prop :=
| R_Typing_Prim : forall prim,
    (R_Primitive prim) hasRefinement (typeOf prim, C_Constraint (C_Prop_Self, (C_Op_Equal, prim)))

| R_Typing_UniOp: forall expr t op t',
    expr hasRefinement t ->
    op maps t to t' ->
    (R_UniOp op expr) hasRefinement t'

| R_Typing_BinOp: forall expr t expr' t' op t'',
    expr hasRefinement t ->
    expr' hasRefinement t' ->
    op maps t and t' to t'' ->
    (R_BinOp op expr expr') hasRefinement t''


where "exp 'hasRefinement' T" := (Refinery_Type_Rule exp T).

