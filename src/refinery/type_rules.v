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



Reserved Notation "exp 'hasRefinement' T" (at level 40).
Inductive Refinery_Type_Rule : Refinery_Lang -> Refinery_RefinementType -> Prop :=
| R_Typing_Prim : forall prim
    (R_Primitive prim) hasRefinement (typeOf prim, C_Constraint (C_Prop_Self, (C_Op_Equal, prim)))

where "exp 'hasRefinement' T" := (Refinery_Type_Rule exp T).

