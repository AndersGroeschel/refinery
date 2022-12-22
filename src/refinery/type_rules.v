Require Import definitions.
Require Import property_logic.


Inductive Refinery_Base_Type: Type :=
| R_T_Int: Refinery_Base_Type
| R_T_Bool: Refinery_Base_Type
.

Definition Refinery_Refinement_Type := (Refinery_Base_Type * Property_Logic)%type.


Reserved Notation "exp 'hasType' T" (at level 40).
Inductive R_Type_Rule : Refinery_Lang -> Refinery_Refinement_Type -> Prop :=
| R_T_Rule_Int : forall z,
    (R_Primitive (R_Int z)) hasType (R_T_Int, (PL_equal PL_self (PL_number z)))

| R_T_Rule_True :
    (R_Primitive (R_Bool true)) hasType (R_T_Bool, (PL_equal PL_self PL_true))

| R_T_Rule_False :
    (R_Primitive (R_Bool false)) hasType (R_T_Bool, (PL_equal PL_self PL_false))

where "exp 'hasType' T" := (R_Type_Rule exp T).

