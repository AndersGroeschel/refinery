Require Import Bool ZArith.
Require Import String.

(* primitives of the language think ints bools floats arrays ... *)
Inductive R_Lang_Primitive : Type :=
    | R_Prim_Bool: bool -> R_Lang_Primitive
.


(* checks if 2 primitive types are the same *)
Definition primitivesSame prim1 prim2 :=
match (prim1, prim2) with 
    | ((R_Prim_Bool true), (R_Prim_Bool true)) => true
    | ((R_Prim_Bool false), (R_Prim_Bool false)) => true
    | _ => false
end.

Theorem primSameEqual_Equivalence:
    forall prim prim',
    (primitivesSame prim prim' = true) <-> (prim = prim').
Proof.
    induction prim; induction prim'; split; intros;
    repeat (match goal with 
    | b: bool |- _ => destruct b
    end; try (reflexivity || discriminate || assumption)).
Qed.



(* the uniary operators of the language *)
Inductive R_Lang_UniOp: Type :=
    | R_Not
.
(* This function defines how uniary operators transform a primitive value *)
Definition uniOpTransformsPrim op prim :=
    match op with 
    | R_Not => match prim with 
        | R_Prim_Bool b => Some (R_Prim_Bool (negb b))
        end
    end.

Inductive R_Lang_BinOp: Type :=
    | R_And
    | R_Or
    | R_Equal
.

Definition binOpTransformsPrim op prim1 prim2 :=
    match op with 
    | R_And => 
        match (prim1,prim2) with 
        | (R_Prim_Bool b1, R_Prim_Bool b2) => Some (R_Prim_Bool (b1 && b2))
        end
    | R_Or => 
        match (prim1,prim2) with 
        | (R_Prim_Bool b1, R_Prim_Bool b2) => Some (R_Prim_Bool (b1 || b2))
        end
    | R_Equal => if primitivesSame prim1 prim2 
        then Some (R_Prim_Bool true) 
        else Some (R_Prim_Bool false)
    end.

(*  The Abstract syntax tree of the language

    programs can be created that are not valid because this structure does not
    impose any rules *)
Inductive Refinery_Lang : Type :=
    | R_Primitive: R_Lang_Primitive -> Refinery_Lang
    | R_Var: string -> Refinery_Lang
    | R_UniOp: R_Lang_UniOp -> Refinery_Lang -> Refinery_Lang
    | R_BinOp: R_Lang_BinOp -> Refinery_Lang -> Refinery_Lang -> Refinery_Lang
.

