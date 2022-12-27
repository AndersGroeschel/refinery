Require Import definitions.



(* the evaluation rules for the language *)
Reserved Notation "c =R=> p" (at level 40).
Inductive Refinery_Eval_Rule: Refinery_Lang -> R_Lang_Primitive -> Prop :=
| R_Eval_Prim: forall prim,
    (R_Primitive prim) =R=> prim

| R_Eval_UniOp: forall expr op prim prim',
    expr =R=> prim -> 
    opTransformsPrim op prim = Some prim' ->

    (R_UniOp op expr) =R=> prim'

where "c =R=> p" := (Refinery_Eval_Rule c p). 

