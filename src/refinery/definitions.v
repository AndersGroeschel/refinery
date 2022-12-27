Require Import Bool ZArith.

(* primitives of the language think ints bools floats arrays ... *)
Inductive R_Lang_Primitive : Type :=
    | R_Prim_Bool: bool -> R_Lang_Primitive
.

(* checks if 2 primitive types are the same *)
Definition primitivesSame prim1 prim2 :=
match (prim1, prim2) with 
    | ((R_Prim_Bool true), (R_Prim_Bool true)) => true
    | ((R_Prim_Bool false), (R_Prim_Bool false)) => false
    | _ => false
end.


(* the uniary operators of the language *)
Inductive R_Lang_UniOp: Type :=
    | R_Not
.
(* This function defines how uniary operators transform a primitive value *)
Definition opTransformsPrim op prim :=
    match op with 
    | R_Not => match prim with 
        | R_Prim_Bool b => Some (R_Prim_Bool (negb b))
        end
    end.


(*  The Abstract syntax tree of the language

    programs can be created that are not valid because this structure does not
    impose any rules *)
Inductive Refinery_Lang : Type :=
    | R_Primitive: R_Lang_Primitive -> Refinery_Lang
    | R_UniOp: R_Lang_UniOp -> Refinery_Lang -> Refinery_Lang
.

