Require Import definitions.
Require Import constraints.

Inductive Refinery_BaseType: Type :=
    | R_T_Bool: Refinery_BaseType
.

Definition typeOf prim :=
    match prim with 
    | R_Prim_Bool _ => R_T_Bool
    end.

Definition Refinery_RefinementType := (Refinery_BaseType * Constraints_Lang)%type.



(* given an input base type what base type is output*)
Definition uniOpTransformBaseType op base :=
    match (op,base) with 
    | (R_Not,R_T_Bool) => Some R_T_Bool
    end.

(* how does an operator transform a primitive *)
Definition opTransformsPrim op prim :=
    match op with 
    | R_Not => match prim with 
        | R_Prim_Bool b => Some (R_Prim_Bool (negb b))
        end
    end.

(* what constraint does the operator enforce on the input *)
Definition uniOpInputConstraint op base := 
    match (op,base) with 
    | (R_Not,R_T_Bool) => Some (C_NoConstraint)
    end
.

(* how does the uniop type *)
Reserved Notation "op 'maps' typ1 'to' typ2" (at level 40).

Inductive R_Type_UniOp_Rule: R_Lang_UniOp -> Refinery_RefinementType -> Refinery_RefinementType -> Prop :=

| R_T_UniOp_Not_NoConstraint: 
    R_Not maps (R_T_Bool,C_NoConstraint) to (R_T_Bool,C_NoConstraint)

| R_T_UniOp_Constraint_Equal: forall op baseIn inputConstraint c_Op prim1 prim2 baseOut,
    uniOpInputConstraint op baseIn = Some inputConstraint ->
    [- C_Constraint (C_Prop_Self, (c_Op, prim1) )-] satisfies [-inputConstraint-] -> 
    opTransformsPrim op prim1 = Some prim2 -> 
    uniOpTransformBaseType op baseIn = Some baseOut ->

    op maps (baseIn, C_Constraint (C_Prop_Self, (c_Op, prim1)))
    to (baseOut,C_Constraint (C_Prop_Self, (c_Op, prim2)))

where "op 'maps' typ1 'to' typ2" := (R_Type_UniOp_Rule op typ1 typ2).








Reserved Notation "exp 'hasRefinement' T" (at level 40).
Inductive Refinery_Type_Rule : Refinery_Lang -> Refinery_RefinementType -> Prop :=
| R_Typing_Prim : forall prim,
    (R_Primitive prim) hasRefinement (typeOf prim, C_Constraint (C_Prop_Self, (C_Op_Equal, prim)))

| R_Typing_UniOp: forall expr t op t',
    expr hasRefinement t ->
    op maps t to t' ->
    (R_UniOp op expr) hasRefinement t'


where "exp 'hasRefinement' T" := (Refinery_Type_Rule exp T).

