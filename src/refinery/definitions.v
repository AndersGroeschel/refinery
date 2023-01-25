Require Import Bool ZArith.

Local Open Scope Z_scope.

(* primitives of the language think ints bools floats arrays ... *)
Inductive R_Lang_Primitive : Type :=
    | R_Prim_Bool: bool -> R_Lang_Primitive
    | R_Prim_Int: Z -> R_Lang_Primitive
.

(* checks if 2 primitive types are the same *)
Definition primitivesSame prim1 prim2 :=
match (prim1, prim2) with 
    | ((R_Prim_Bool true), (R_Prim_Bool true)) => true
    | ((R_Prim_Bool false), (R_Prim_Bool false)) => true
    | (R_Prim_Int z1, R_Prim_Int z2) => z1 =? z2
    | _ => false
end.

Theorem primSameEqual_Equivalence:
    forall prim prim',
    (primitivesSame prim prim' = true) <-> (prim = prim').
Proof.
    induction prim; induction prim'; split; intros;
    repeat (match goal with 
    | b: bool |- _ => destruct b
    | H: R_Prim_Int _ = R_Prim_Int _ |- _ => inversion H; subst; clear H
    | |- primitivesSame (R_Prim_Int ?z) (R_Prim_Int ?z) = true =>
    let H := fresh "H" in 
    assert (z0 = z0) as H; [
        reflexivity 
        | apply Z.eqb_eq in H; unfold primitivesSame
    ]
    | H : context [primitivesSame (R_Prim_Int ?z) (R_Prim_Int ?z')] |- R_Prim_Int ?z = R_Prim_Int ?z' => 
        unfold primitivesSame in H;apply Z.eqb_eq in H; subst
    end; try (reflexivity || discriminate || assumption)).
    
    Qed.

(* the base types of the type system*)
Inductive Refinery_BaseType: Type :=
    | R_T_Bool: Refinery_BaseType
    | R_T_Int: Refinery_BaseType
.

Notation "'Bool'" := R_T_Bool.
Notation "'Int'" := R_T_Int.

(* gives the base type of a primitive value *)
Definition baseTypeOf prim :=
    match prim with 
    | R_Prim_Bool _ => R_T_Bool
    | R_Prim_Int _ => R_T_Int
    end.

Definition baseTypesSame t1 t2 :=
    match (t1,t2) with 
    | (R_T_Bool, R_T_Bool) => true
    | (R_T_Int, R_T_Int) => true
    | _ => false
    end.



(* the uniary operators of the language *)
Inductive R_Lang_UniOp: Type :=
    | R_Not
.
(* This function defines how uniary operators transform a primitive value *)
Definition uniOpTransformsPrim op prim :=
    match op with 
    | R_Not => match prim with 
        | R_Prim_Bool b => Some (R_Prim_Bool (negb b))
        | _ => None
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
        | _ => None
        end
    | R_Or => 
        match (prim1,prim2) with 
        | (R_Prim_Bool b1, R_Prim_Bool b2) => Some (R_Prim_Bool (b1 || b2))
        | _ => None
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
    | R_UniOp: R_Lang_UniOp -> Refinery_Lang -> Refinery_Lang
    | R_BinOp: R_Lang_BinOp -> Refinery_Lang -> Refinery_Lang -> Refinery_Lang
.

