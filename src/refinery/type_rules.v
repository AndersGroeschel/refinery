Require Import definitions.
Require Import constraints.

Inductive Refinery_BaseType: Type :=
    | R_T_Bool: Refinery_BaseType
.

Definition Refinery_RefinementType := (Refinery_BaseType * Constraints_Lang)%type.



Reserved Notation "exp 'hasRefinement' T" (at level 40).
Inductive Refinery_Type_Rule : Refinery_Lang -> Refinery_RefinementType -> Prop :=
    | R_T_Rule_True :
        (R_Primitive (R_Prim_Bool true)) hasRefinement (R_T_Bool, C_Constraint (C_Prop_Self, (C_Op_Equal, R_Prim_Bool true)))

    | R_T_Rule_False :
        (R_Primitive (R_Prim_Bool false)) hasRefinement (R_T_Bool, C_Constraint (C_Prop_Self,( C_Op_Equal, R_Prim_Bool false)))

where "exp 'hasRefinement' T" := (Refinery_Type_Rule exp T).

