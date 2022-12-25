Require Import Bool ZArith.


Inductive R_Lang_Primitive : Type :=
    | R_Prim_Bool: bool -> R_Lang_Primitive
.

Definition primitivesSame prim1 prim2 :=
match (prim1, prim2) with 
    | ((R_Prim_Bool true), (R_Prim_Bool true)) => true
    | ((R_Prim_Bool false), (R_Prim_Bool false)) => false
    | _ => false
end.

Inductive R_Lang_UniOp: Type :=
    | R_Not
.


Inductive Refinery_Lang : Type :=
    | R_Primitive: R_Lang_Primitive -> Refinery_Lang
    | R_UniOp: R_Lang_UniOp -> Refinery_Lang -> Refinery_Lang
.

