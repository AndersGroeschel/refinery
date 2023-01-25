Require Import definitions.
Require Import constraints.


Definition Refinery_RefinementType := (Refinery_BaseType * Constraints_Lang)%type.


(* This inductive defines how a uniary operator takes a type to a type *)
Reserved Notation "op 'maps' typ1 'to' typ2" (at level 40).

Inductive R_Type_UniOp_Rule: R_Lang_UniOp -> Refinery_RefinementType -> Refinery_RefinementType -> Prop :=

| R_T_UniOp_Not_NoConstraint: 
    R_Not maps (bool, [- Any -]) to (bool, [- Any -])

| R_T_UniOp_Not_Equal: forall b C,
    C equivalentTo [- self == (R_Prim_Bool b) -] ->
    R_Not maps (bool, C ) to (bool,[- self == (R_Prim_Bool (negb b)) -])

where "op 'maps' typ1 'to' typ2" := (R_Type_UniOp_Rule op typ1 typ2).

(* This inductive defines how a uniary operator takes a type to a type *)
Reserved Notation "op 'maps' typ1 'and' typ2 'to' typ3" (at level 40).

Inductive R_Type_BinOp_Rule: R_Lang_BinOp -> Refinery_RefinementType -> Refinery_RefinementType -> Refinery_RefinementType -> Prop :=

| R_T_BinOp_And_False: forall C C',
    (C equivalentTo [- self == (R_Prim_Bool false) -]) \/ (C' equivalentTo [- self == (R_Prim_Bool false) -]) ->
    R_And maps (bool, C) and (bool, C') to (bool,[- self == (R_Prim_Bool false) -])
| R_T_BinOp_And_True: forall C C',
    (C equivalentTo [- self == (R_Prim_Bool true) -]) /\ (C' equivalentTo [- self == (R_Prim_Bool true) -]) ->
    R_And maps (bool, C) and (bool, C') to (bool, [- self == (R_Prim_Bool true) -])

| R_T_BinOp_And_NoConstraint: forall C C',
    R_And maps (bool, C ) and (bool, C') to (bool,[- Any -])


| R_T_BinOp_Or_False: forall C C',
    (C equivalentTo [- self == (R_Prim_Bool false) -]) /\ (C' equivalentTo [- self == (R_Prim_Bool false) -])   ->
    R_Or maps (bool, C) and (bool, C') to (bool,[- self == (R_Prim_Bool false) -])
| R_T_BinOp_Or_True_True: forall C C',
    (C equivalentTo [- self == (R_Prim_Bool true) -]) \/ (C' equivalentTo [- self == (R_Prim_Bool true) -]) ->
    R_Or maps (bool, C) and (bool, C') to (bool, [- self == (R_Prim_Bool true) -])

| R_T_BinOp_Or_NoConstraint: forall C C',
    R_Or maps (bool, C ) and (bool, C') to (bool,[- Any -])


| R_T_BinOp_Equal_False_TypeDifferent: forall typ typ' C C',
    typ <> typ' ->
    R_Equal maps (typ, C) and (typ', C') to (bool, [- self == (R_Prim_Bool false) -])

| R_T_BinOp_Equal_False_Excludes: forall typ C C',
    C excludes C' \/ C' excludes C -> 
    R_Equal maps (typ,C) and (typ,C') to (bool, [- self == (R_Prim_Bool false) -])

| R_T_BinOp_Equal_True: forall typ prim C C',
    C equivalentTo [- self == prim -] ->
    C' equivalentTo [- self == prim -] -> 
    R_Equal maps (typ,C) and (typ, C') to (bool, [- self == (R_Prim_Bool true) -])

| R_T_BinOp_Equal_NoConstraint: forall typ C C',
    R_Equal maps (typ,C) and (typ,C') to (bool, [- Any -])

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

