Require Import definitions.
Require Import Bool.
Require Import ZArith.
Require Import regex.
Require Import customTactics.

Local Open Scope Z_scope.

(*  the constraits part of the language is maybe the most important 
    thing to understand. This is how refinemnents are made to base types.
    We constrain the type by applying operators onto the properties of 
    that type, for example true would have the constraint that self = true.
    *)


(* the property of a type that we are constraining *)
Inductive C_Lang_Property : Type := 
    | C_Prop_Self: C_Lang_Property
.
(* check if properties are the same *)
Definition propertiesSame prop1 prop2 := 
match (prop1, prop2) with 
    | (C_Prop_Self,C_Prop_Self) => true
end.

(* relationships properties can have ex: prop = 7 *)
Inductive C_Lang_Operator: Type :=
| C_Op_Equal
| C_Op_NotEqual
| C_Op_LessThan
| C_Op_LessThanEqual
| C_Op_GreaterThan
| C_Op_GreaterThanEqual
.

(* take a relationship and do the oposite*)
Definition negateOp op :=
    match op with 
    | C_Op_Equal => C_Op_NotEqual
    | C_Op_NotEqual => C_Op_Equal
    | C_Op_LessThan => C_Op_GreaterThanEqual
    | C_Op_LessThanEqual => C_Op_GreaterThan
    | C_Op_GreaterThan => C_Op_LessThanEqual
    | C_Op_GreaterThanEqual => C_Op_LessThan
    end.

Definition cOpsEqual op1 op2 := 
    match (op1, op2) with 
    | (C_Op_Equal,C_Op_Equal) => true
    | (C_Op_NotEqual,C_Op_NotEqual) => true
    | (C_Op_LessThan,C_Op_LessThan) => true
    | (C_Op_LessThanEqual,C_Op_LessThanEqual) => true
    | (C_Op_GreaterThan,C_Op_GreaterThan) => true
    | (C_Op_GreaterThanEqual,C_Op_GreaterThanEqual) => true
    | _ => false
    end.

Definition simpleConstraint := (C_Lang_Property * (C_Lang_Operator * R_Lang_Primitive))%type.

(* this is the core of the constraints language
    a type can either have no constraint or a single constraint *)
Inductive Constraints_Lang: Type :=
| C_NoConstraint: Constraints_Lang
| C_Constraint: simpleConstraint -> Constraints_Lang
| C_And: Constraints_Lang -> Constraints_Lang -> Constraints_Lang
| C_Or: Constraints_Lang -> Constraints_Lang -> Constraints_Lang
.

Declare Custom Entry constraint.

Notation " '[-' x '-]' " := (x) (at level 0, x custom constraint at level 99).
Notation "( x )" := x (in custom constraint, x at level 99).
Notation "x" := x (in custom constraint at level 0, x constr at level 0).
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom constraint at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9).

Notation " 'Any' " := C_NoConstraint (in custom constraint).
Notation " 'self' " := C_Prop_Self (in custom constraint).
Notation " 'true' " := (R_Prim_Bool true) (in custom constraint).
Notation " 'false' " := (R_Prim_Bool false) (in custom constraint).
Notation " 'Bool' b " :=  (R_Prim_Bool b) (in custom constraint at level 60, no associativity).
Notation " 'Int' z " :=  (R_Prim_Int z) (in custom constraint at level 60, no associativity).

Notation "x && y"  := (C_And x y) (in custom constraint at level 80, left associativity).
Notation "x || y"  := (C_Or x y) (in custom constraint at level 80, left associativity).

Notation " prop '==' prim " := (C_Constraint (prop, (C_Op_Equal, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '!=' prim " := (C_Constraint (prop, (C_Op_NotEqual, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '<' prim " := (C_Constraint (prop, (C_Op_LessThan, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '>' prim " := (C_Constraint (prop, (C_Op_GreaterThan, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '<=' prim " := (C_Constraint (prop, (C_Op_LessThanEqual, prim))) (in custom constraint at level 70, no associativity).
Notation " prop '>=' prim " := (C_Constraint (prop, (C_Op_GreaterThanEqual, prim))) (in custom constraint at level 70, no associativity).

Definition IsNumberType prim := match prim with 
| R_Prim_Int _ => True 
| _ => False
end.

Definition PrimLe prim1 prim2 := match (prim1, prim2) with 
| (R_Prim_Int z1, R_Prim_Int z2) => z1 < z2
| _ => False
end.

Definition PrimGe prim1 prim2 := match (prim1, prim2) with 
| (R_Prim_Int z1, R_Prim_Int z2) => z1 > z2
| _ => False
end.

Inductive C_Types: Type :=
| C_Type_Bool: C_Types
| C_Type_Int: C_Types
.
Definition typeOfPrim prim := 
    match prim with 
    | R_Prim_Bool _ => C_Type_Bool
    | R_Prim_Int _ => C_Type_Int
    end.

Definition sameType typ1 typ2 :=
    match (typ1,typ2) with
    | (C_Type_Bool, C_Type_Bool) => true
    | (C_Type_Int, C_Type_Int) => true
    | _ => false
    end.

Inductive C_TypeList: Type :=
| C_Type_None: C_TypeList
| C_Type_Any: C_TypeList
| C_Type_Seq: C_Types -> C_TypeList -> C_TypeList
.

Fixpoint removeItemFromSequence seq item := 
    match seq with 
    | C_Type_None => C_Type_None
    | C_Type_Any => C_Type_Any
    | C_Type_Seq typ rest => if sameType typ item 
                        then removeItemFromSequence rest item
                        else C_Type_Seq typ (removeItemFromSequence rest item)
    end.

Fixpoint TypeInList lst search := match lst with 
| C_Type_None => False
| C_Type_Any => True
| C_Type_Seq typ lst' => typ = search \/ (TypeInList lst' search)
end.

Fixpoint containsType lst typ :=
    match lst with 
    | C_Type_None => false
    | C_Type_Any => true
    | C_Type_Seq type lst' => 
        if sameType typ type then true 
        else containsType lst' typ
    end.

Lemma ContainsSame: 
    forall lst typ,
    TypeInList lst typ <-> (containsType lst typ = true).
Proof.
    intros lst typ. split; intro H; 
    induction lst; try (reflexivity || contradiction || discriminate). 
    - simpl in *; destruct H.
        + subst. destruct typ; reflexivity.
        + specialize (IHlst H). rewrite IHlst.
            destruct (sameType typ c); reflexivity.
    - destruct typ; destruct c; simpl; 
        try solve[left; reflexivity]; 
        right; apply IHlst; simpl in H; assumption.
Qed.

Fixpoint BaseIsAny A := match A with 
| C_Type_None => False
| C_Type_Any => True 
| C_Type_Seq typ rest => BaseIsAny rest
end.

Theorem BaseAnyHasAny:
    forall A elem,
    BaseIsAny A ->
    TypeInList A elem.
Proof.
    induction A;
    intros elem H_any;
    try (contradiction || reflexivity).
    simpl. right. apply IHA. simpl in H_any. assumption.
Qed.
    


Fixpoint subset_func A B :=
    match A with 
    | C_Type_None => True
    | C_Type_Any => BaseIsAny B
    | C_Type_Seq type A' => (TypeInList B type) /\ subset_func A' B 
    end.

Notation "A 'subset' B" := (subset_func A B) (at level 40).

Theorem NoneSubsetOfOnlyNone:
    forall A,
    A subset C_Type_None ->
    A = C_Type_None.
Proof.
    induction A; intros H; try (reflexivity || contradiction).
    - simpl in H. destruct H. contradiction. 
Qed.

Theorem allSubsetOfAny:
    forall A, 
    A subset C_Type_Any.
Proof.
    intros A.
    induction A; simpl; 
    try split; try reflexivity; 
    try assumption.
Qed.

Theorem allSubsetOfBaseAny:
    forall A B, 
    BaseIsAny B ->
    A subset B.
Proof.
    intros A.
    induction A; intros B H; simpl; 
    try split; try reflexivity; 
    try assumption.
    - induction B; try contradiction; try assumption.
        simpl. right. apply IHB. assumption.
    - apply IHA. assumption.  
Qed.

Theorem AnySubsetOfOnlyAny:
    forall A, 
    C_Type_Any subset A ->
    BaseIsAny A.
Proof.
    intros. simpl in *. assumption.
Qed.

Theorem RemovePreserveSubset:
    forall A B elem,
    A subset B ->
    (removeItemFromSequence A elem) subset B.
Proof.
    induction A;
    intros B elem H; logicAuto_NoSpecialize;
    try apply IHA;
    assumption.
Qed.

Theorem SubsetReverseRemoval:
    forall A B elem,
    TypeInList B elem ->
    (removeItemFromSequence A elem) subset B ->
    A subset B.
Proof.
    induction A; intros B elem H_type H_subset;
    logicAuto_NoSpecialize; destruct c; destruct elem; simpl in *;
    try destruct H_subset;
    try assumption;
    try solve [eapply IHA; unifyAssumption].
    - eapply IHA; [apply H_type |]; assumption. 
    - eapply IHA; [apply H_type |]; assumption.
Qed. 



Theorem seqInversion :
    forall A B elem,
    A subset (C_Type_Seq elem B) ->
    A subset B \/ ((TypeInList A elem) /\ (removeItemFromSequence A elem) subset B).
Proof.
    induction A;
    intros B elem H_subset.
    - logicAuto.
    - apply AnySubsetOfOnlyAny in H_subset. logicAuto. 
    - logicAuto_NoSpecialize; apply IHA in H0; 
        logicAuto_NoSpecialize; try solve [destruct c; discriminate].
        right; logicAuto_NoSpecialize.
        apply RemovePreserveSubset. assumption.
Qed.


Theorem  subsetTransitive:
    forall A B C,
    A subset B ->
    B subset C ->
    A subset C.
Proof.
    intros A B.
    generalize dependent A.
    induction B; intros A C H H0.
    - apply NoneSubsetOfOnlyNone in H; subst; assumption.
    - apply AnySubsetOfOnlyAny in H0. induction A; auto.
        simpl. split.
        + induction C; try (reflexivity || contradiction).
            simpl in H0. simpl. right. apply BaseAnyHasAny. assumption.
        + apply IHA. apply allSubsetOfAny.
    - apply seqInversion in H. logicAuto_NoSpecialize.
        + apply IHB; assumption.
        + eapply IHB in H2; [| unifyAssumption]. 
        eapply SubsetReverseRemoval; unifyAssumption.            
Qed.

Theorem seqPreserveSubset:
    forall A B elem,
    A subset B ->
    A subset (C_Type_Seq elem B).
Proof.
    induction A; intros B elem H_subset.
    - reflexivity.
    - apply AnySubsetOfOnlyAny in H_subset. simpl; assumption.
    - simpl in *; destruct H_subset; split.
        + right. assumption.
        + apply IHA. assumption.
Qed.

Theorem selfSubset:
    forall A,
    A subset A.
Proof.
    intros A.
    induction A; try reflexivity.
    simpl; split.
    - left. reflexivity.
    - apply seqPreserveSubset. assumption.
Qed.



Fixpoint filterTypes lst (filter :(C_Types -> bool)) := 
    match lst with 
    | C_Type_None => C_Type_None
    | C_Type_Any => C_Type_Any 
    | C_Type_Seq typ lst' => 
        if filter typ 
        then C_Type_Seq typ (filterTypes lst' filter)
        else filterTypes lst' filter
    end.

Fixpoint typeIntersection typeList1 typeList2 :=
    match typeList1 with 
    | C_Type_None => C_Type_None
    | C_Type_Any => typeList2
    | C_Type_Seq type1 lst1 => match typeList2 with 
        | C_Type_None => C_Type_None
        | C_Type_Any => typeList1
        | C_Type_Seq type2 lst2 => 
            if (containsType typeList2 type1) 
            then C_Type_Seq type1 (typeIntersection lst1 typeList2)
            else typeIntersection lst1 typeList2
        end
    end.

Theorem bothContainIntersectionContains: 
    forall lst1 lst2 typ,
    TypeInList lst1 typ ->
    TypeInList lst2 typ ->
    TypeInList (typeIntersection lst1 lst2) typ.
Proof.
    intros lst1 lst2 typ H_typ1 H_typ2.
    induction lst1; induction lst2;
    try (contradiction || discriminate || assumption).
    simpl in H_typ1; simpl in H_typ2; 
    logicAuto. 
    - destruct typ; simpl; left; reflexivity.
    - destruct c; destruct typ; simpl; try solve [left; reflexivity].
        + destruct (containsType lst2 C_Type_Bool);[right|];assumption.
        + destruct (containsType lst2 C_Type_Int);[right|];assumption.
    - simpl; destruct typ; destruct c0; simpl; 
        try solve [left; reflexivity];
        try solve [apply ContainsSame in H; rewrite H; left; reflexivity].
    - simpl. destruct (sameType c c0) eqn: Heq.
        + right. assumption.
        +  destruct (containsType lst2 c) eqn: Heq0.
            * right. assumption.
            * assumption.
Qed.  

Theorem intersectionSubsetOfOriginals : 
    forall t1 t2 t3,
    typeIntersection t1 t2 = t3 ->
    t3 subset t1 /\ t3 subset t2.
Proof.
    induction t1;
    intros t2 t3 H_intersect; split;
    simpl in H_intersect; subst.
    - apply selfSubset.
    - reflexivity.
    - apply allSubsetOfAny.
    - apply selfSubset.
    - induction t2.
        + reflexivity.
        + apply selfSubset.
        + destruct (containsType (C_Type_Seq c0 t2) c).
            * simpl; split; [left; reflexivity|].
                assert(typeIntersection t1 (C_Type_Seq c0 t2) = typeIntersection t1 (C_Type_Seq c0 t2)); [reflexivity|].
                apply IHt1 in H. destruct H.
                apply seqPreserveSubset; assumption.
            *   assert(typeIntersection t1 (C_Type_Seq c0 t2) = typeIntersection t1 (C_Type_Seq c0 t2)); [reflexivity|].
                apply IHt1 in H. destruct H.
                apply seqPreserveSubset; assumption.
    - induction t2.
        + reflexivity.
        + apply allSubsetOfAny.
        + destruct (containsType (C_Type_Seq c0 t2) c) eqn: eq.
            * simpl; split.
                -- apply ContainsSame in eq. simpl in eq. assumption.
                -- assert(typeIntersection t1 (C_Type_Seq c0 t2) = typeIntersection t1 (C_Type_Seq c0 t2));[reflexivity|].
                    apply IHt1 in H; destruct H.
                    assumption.
            * assert(typeIntersection t1 (C_Type_Seq c0 t2) = typeIntersection t1 (C_Type_Seq c0 t2));[reflexivity|].
                apply IHt1 in H; destruct H.
                assumption.
Qed.

Definition TypeListEquivalence t1 t2 := match (t1,t2) with 
| (C_Type_Any, t2) => BaseIsAny t2
| (t1,C_Type_Any) => BaseIsAny t1
| _ => t1 subset t2 /\ t2 subset t1
end.
(**
Theorem IntersectionAnyUnchanged: .
Proof.
    
Qed.
*)

(*
Theorem subsetImpliesIntersection:
    forall t1 t2,
    t1 subset t2 ->
    exists t3, TypeListEquivalence t1 (typeIntersection t2 t3).
Proof.
    induction t1;
    intros t2 H.
    - exists C_Type_None. destruct t2; 
        unfold TypeListEquivalence; simpl; split; assumption.
    - apply AnySubsetOfOnlyAny in H.
        induction t2; try (contradiction).
        + exists C_Type_Any. reflexivity.
        + simpl in H. apply IHt2 in H. destruct H.
            unfold TypeListEquivalence in *.
            exists x.
            induction x; destruct t2; 
            logicAuto_NoSpecialize.
    - destruct H. apply IHt1 in H0. destruct H0.
        induction t2; try contradiction.
        + simpl. exists (C_Type_Seq c t1); split; apply selfSubset.
        + destruct H.
            * subst. exists (C_Type_Seq c x).
                clear IHt2.
                clear IHt1.
                induction x.
                -- simpl in H0. destruct t1; 
                    try contradiction. simpl; logicAuto;
                    try solve [destruct c; discriminate].
                    ++ split; simpl; split; 
                        try solve[ left; reflexivity];
                        try reflexivity.
                        induction t2; logicAuto_NoSpecialize.
                        left. 
                        destruct c0; destruct c; try discriminate;
                        try reflexivity.
                    ++ destruct H0. logicAuto_NoSpecialize.
                -- simpl in *. destruct t1; 
                    logicAuto_NoSpecialize;
                    try solve[destruct c; discriminate];
                    try solve[destruct H0; logicAuto_NoSpecialize].
                    ++ clear eq; split;[| apply allSubsetOfBaseAny; reflexivity].
                        simpl; split; [left;reflexivity|].
                        unfold TypeListEquivalence in H0.
                        induction t2; 
                        try (contradiction || reflexivity).
                        simpl; destruct (sameType c0 c) eqn: eq; 
                        simpl; apply IHt2;
                        simpl in *; assumption.
                    ++ clear eq.
                        split; logicAuto_NoSpecialize.
                        ** destruct H0.  
                            logicAuto_NoSpecialize.
                            right.
                            apply bothContainIntersectionContains; [| logicAuto_NoSpecialize].
                            assumption.
                        ** destruct H0.
                            induction t2; simpl; 
                            logicAuto_NoSpecialize;
                            try solve [apply allSubsetOfBaseAny; reflexivity].

                            try solve [
                            (eapply subsetTransitive; [| apply seqPreserveSubset; apply selfSubset]);
                            apply bothContainIntersectionContains; [| logicAuto_NoSpecialize]].



    
            
            logicAuto_NoSpecialize.
                -- split;[ simpl; split; [ left; reflexivity|] |].
    
    
    
    
    simpl in H; destruct H. apply IHt1 in H0.
        destruct H0.
        exists (C_Type_Seq c x).
        assert( TypeInList (C_Type_Seq c x) c); [left; reflexivity |].
        induction t2; simpl in *; unfold TypeListEquivalence in *;
        try (contradiction || discriminate); 
        repeat split; try assumption. 
        + destruct t1; destruct x; logicAuto_NoSpecialize;
            try solve [apply allSubsetOfBaseAny; reflexivity];
            try solve [eapply subsetTransitive; [unifyAssumption| apply seqPreserveSubset; apply selfSubset]].
        + simpl. left. reflexivity.
        + destruct t1; logicAuto_NoSpecialize; 
            try solve [apply allSubsetOfBaseAny; reflexivity];
            destruct x; logicAuto_NoSpecialize;
            try solve [eapply subsetTransitive; [unifyAssumption| apply seqPreserveSubset; apply selfSubset]].
        + logicAuto_NoSpecialize;
            try solve[ destruct c; simpl in *; discriminate];
            destruct x; destruct t1;
            logicAuto_NoSpecialize;
            repeat match goal with 
            | H: BaseIsAny (C_Type_Seq _ _) |- _ => simpl in H
            end.
            simpl in *; try (contradiction || reflexivity).

    *)




Definition NumberType := (C_Type_Seq C_Type_Int C_Type_None).

Definition single typ := (C_Type_Seq typ C_Type_None).

Reserved Notation "C 'typedAs' t" (at level 40).
Inductive C_TypesTo: Constraints_Lang -> C_TypeList -> Prop :=
| C_TypesTo_NoConstraint: 
    [- Any -] typedAs C_Type_Any

| C_TypesTo_Equal: forall prim prop,
    [- prop == prim -] typedAs if containsType NumberType (typeOfPrim prim) 
                                then NumberType 
                                else single (typeOfPrim prim)

| C_TypesTo_NotEqual: forall prim prop,
    [- prop != prim -] typedAs if containsType NumberType (typeOfPrim prim) 
                                then NumberType 
                                else single (typeOfPrim prim)

| C_TypesTo_And: forall C1 C2 t1 t2,
    C1 typedAs t1 ->
    C2 typedAs t2 ->
    [- C1 && C2 -] typedAs (typeIntersection t1 t2)

| C_TypesTo_Or: forall C1 C2 t1 t2,
    C1 typedAs t1 ->
    C2 typedAs t2 ->
    [- C1 || C2 -] typedAs (typeIntersection t1 t2)

| C_TypesTo_Le: forall prim prop,
    IsNumberType prim ->
    [- prop < prim -] typedAs NumberType
| C_TypesTo_LeEq: forall prim prop,
    IsNumberType prim ->
    [- prop <= prim -] typedAs NumberType

| C_TypesTo_Ge: forall prim prop,
    IsNumberType prim ->
    [- prop > prim -] typedAs NumberType
| C_TypesTo_GeEq: forall prim prop,
    IsNumberType prim ->
    [- prop >= prim -] typedAs NumberType
where "C 'typedAs' t" := (C_TypesTo C t).

Theorem ConstraintsOneTyping:
    forall C t1 t2,
    C typedAs t1 ->
    C typedAs t2 ->
    t1 = t2.
Proof.
    intros C t1 t2 H_type1 H_type2.
    generalize dependent t2.
    induction H_type1; subst; 
    let t := fresh "t" in intros t H_type2;
    try solve[ inversion H_type2; reflexivity];
    inversion H_type2; subst;
    repeat match goal with 
    | IH: forall t, ?C typedAs t -> ?t0 = t,
        H: ?C typedAs ?t1 |- _ =>
        apply IH in H
    end; subst;
    reflexivity.
Qed.
(*
Theorem OrMakesSense:
    forall C1 C2 t1 t2,
    C1 typedAs t1 ->
    C2 typedAs t2 ->
    exists C3 t3,
        C3 typedAs t3 -> 
        [-C2 || C3-] typedAs t1.
Proof.
    intros C1 C2 t1 t2 H_type1 H_type2.
    induction H_type2; inversion H_type1; subst.
    match goal with 
    | H_type: ?C typedAs ?t |-
        exists C' t',
        C' typedAs t' -> [- Any || C' -] typedAs ?t => 
            exists C; exists t;
            assert ((typeIntersection C_Type_Any t) = t)
    end.
    -  
Qed.

*)

Reserved Notation "a 'elementOf' C" (at level 40).
Inductive C_ElementOf_Rules: R_Lang_Primitive -> Constraints_Lang -> Prop :=
| C_ElementOf_NoConstraint: forall a,
    a elementOf [- Any -]
| C_ElementOf_Equal: forall a,
    a elementOf [- self == a -]

| C_ElementOf_And: forall a C1 C2,
    a elementOf C1 ->
    a elementOf C2 ->
    a elementOf [- C1 && C2 -]

| C_ElementOf_Or_Left: forall a C1 C2 t,
    [- C1 || C2 -] typedAs t ->
    TypeInList t (typeOfPrim a)  ->
    a elementOf C1 ->
    a elementOf [- C1 || C2 -]

| C_ElementOf_Or_Right: forall a C1 C2 t,
    [- C1 || C2 -] typedAs t ->
    TypeInList t (typeOfPrim a)  ->
    a elementOf C2 ->
    a elementOf [- C1 || C2 -]

| C_ElementOf_NotEqual: forall a b,
    a <> b ->
    typeOfPrim a = typeOfPrim b ->
    a elementOf [- self != b -]

| C_ElementOf_Le: forall prim1 prim2,
    PrimLe prim1 prim2 ->
    prim1 elementOf [- self < prim2 -]
| C_ElementOf_LeEq: forall prim1 prim2,
    IsNumberType prim1 ->
    IsNumberType prim2 ->
    PrimLe prim1 prim2 \/ (prim1 = prim2) ->
    prim1 elementOf [- self <= prim2 -]

| C_ElementOf_Ge: forall prim1 prim2,
    PrimGe prim1 prim2 ->
    prim1 elementOf [- self > prim2 -]
| C_ElementOf_GeEq: forall prim1 prim2,
    IsNumberType prim1 ->
    IsNumberType prim2 ->
    PrimGe prim1 prim2 \/ (prim1 = prim2) ->
    prim1 elementOf [- self >= prim2 -]

where "a 'elementOf' C" := (C_ElementOf_Rules a C). 

Theorem typing_matters:
    forall C t elem, 
    C typedAs t ->
    elem elementOf C ->
    TypeInList t (typeOfPrim elem).
Proof.
    intros C t elem H_type H_element.
    induction H_type;
    try solve[
        destruct prim; try contradiction;
        destruct elem;
        (inversion H_element; subst; contradiction ||
        simpl;left;reflexivity)
    ].
    - reflexivity.
    - destruct prim;destruct elem; simpl; left; try reflexivity.
        + inversion H_element; subst. discriminate.
        + inversion H_element; subst. discriminate.
    - inversion H_element; subst.
        logicAuto.
        apply bothContainIntersectionContains; assumption.
    - inversion H_element; subst;
        repeat match goal with 
        | H: [- ?C1 || ?C2 -] typedAs ?t |- _ => inversion H; subst; clear H
        | H: ?C typedAs ?t, H0: ?C typedAs ?t0 |- _ =>
            assert (t = t0); [apply (ConstraintsOneTyping C t t0); assumption | subst; clear H0]
        end;
        assumption.
Qed.


Theorem or_inversion:
    forall C1 C2 a,
    a elementOf [- C1 || C2 -] ->
    a elementOf C1 \/ a elementOf C2.
Proof.
    intros C1 C2 a H.
    inversion H; subst.
    - left. assumption.
    - right. assumption.  
Qed.

(*
 ###### NEED TO ADD TYPING
*)

Reserved Notation "C1 'satisfies' C2" (at level 40).
Inductive C_Satisfy_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=

| C_Satisfies_Equal: forall C,
    C satisfies C
| C_Satisfies_Any: forall C,
    C satisfies [- Any -]

| C_Satisfies_NeqBool: forall b C,
    C satisfies [- self == (Bool b) -] ->
    C satisfies [- self != (Bool (negb b)) -]

| C_Satisfies_AnyBool: forall C,
    C typedAs (single C_Type_Bool) ->
    C satisfies [- self == true || self == false -]

| C_Satisfies_AndRight: forall C1 C2 C3,
    C1 satisfies C2 ->
    C1 satisfies C3 ->
    C1 satisfies [- C2 && C3 -]
| C_Satisfies_AndLeft_Left: forall C1 C2 C3 C,
    C1 satisfies C3 ->
    C satisfies [- C1 && C2 -] ->
    C satisfies C3
| C_Satisfies_AndLeft_Right: forall C1 C2 C3 C,
    C2 satisfies C3 ->
    C satisfies [- C1 && C2 -] ->
    C satisfies C3

| C_Satisfies_OrRight_Left: forall C1 C2 C3 t,
    [- C2 || C3 -] typedAs t ->
    C1 satisfies C2 ->
    C1 satisfies [- C2 || C3 -]
| C_Satisfies_OrRight_Right: forall C1 C2 C3 t,
    [- C2 || C3 -] typedAs t ->
    C1 satisfies C3 ->
    C1 satisfies [- C2 || C3 -]
| C_Satisfies_OrLeft: forall C1 C2 C3 C,
    C1 satisfies C3 ->
    C2 satisfies C3 ->
    C satisfies [- C1 || C2 -] ->
    C satisfies C3

| C_Satisfies_Le_Le: forall prim1 prim2 prop C,
    PrimLe prim1 prim2 -> 
    C satisfies [- prop < prim1 -] ->
    C satisfies [- prop < prim2 -]
| C_Satisfies_Le_Neq: forall prim1 prim2 prop C,
    PrimLe prim1 prim2 -> 
    C satisfies [- prop < prim1 -] ->
    C satisfies [- prop != prim2 -]
| C_Satisfies_Eq_Le: forall prim1 prim2 prop C,
    PrimLe prim1 prim2 -> 
    C satisfies [- prop == prim1 -] ->
    C satisfies [- prop < prim2 -]

| C_Satisfies_Le_LeEq: forall prim prop C,
    IsNumberType prim -> 
    C satisfies [- prop < prim -] ->
    C satisfies [- prop <= prim -]
| C_Satisfies_Eq_LeEq: forall prim prop C,
    IsNumberType prim ->
    C satisfies [- prop == prim -] -> 
    C satisfies [- prop <= prim -]

| C_Satisfies_LeAnd_Le_Int: forall z prop C,
    C satisfies [- prop < Int z && prop != Int (Z.sub z 1) -] ->
    C satisfies [- prop < Int (Z.sub z 1) -]

| C_Satisfies_LeEq_LeOr_Int: forall z prop C,
    C satisfies [- prop <= Int z -] ->
    C satisfies [- prop < Int z || prop == Int z -]



| C_Satisfies_Ge_Ge: forall prim1 prim2 prop C,
    PrimGe prim1 prim2 -> 
    C satisfies [- prop > prim1 -] ->
    C satisfies [- prop > prim2 -]
| C_Satisfies_Ge_Neq: forall prim1 prim2 prop C,
    PrimGe prim1 prim2 -> 
    C satisfies [- prop > prim1 -] ->
    C satisfies [- prop != prim2 -]
| C_Satisfies_Eq_Ge: forall prim1 prim2 prop C,
    PrimGe prim1 prim2 -> 
    C satisfies [- prop == prim1 -] ->
    C satisfies [- prop > prim2 -]

| C_Satisfies_Ge_GeEq: forall prim prop C,
    IsNumberType prim -> 
    C satisfies [- prop > prim -] ->
    C satisfies [- prop >= prim -]
| C_Satisfies_Eq_GeEq: forall prim prop C,
    IsNumberType prim ->
    C satisfies [- prop == prim -] -> 
    C satisfies [- prop >= prim -]

| C_Satisfies_GeAnd_Ge_Int: forall z prop C,
    C satisfies [- prop > Int z && prop != Int (Z.add z 1) -] ->
    C satisfies [- prop > Int (Z.add z 1) -]

| C_Satisfies_GeEq_GeOr_Int: forall z prop C,
    C satisfies [- prop >= Int z -] ->
    C satisfies [- prop > Int z || prop == Int z -]

where "C1 'satisfies' C2" := (C_Satisfy_Rules C1 C2).


Theorem SatisfyTransitive:
    forall C1 C2 C3,
        C1 satisfies C2 ->
        C2 satisfies C3 ->
        C1 satisfies C3.
Proof.
    intros C1 C2 C3 H H0.
    induction H0; logicAuto; eauto using C_Satisfy_Rules.
Qed.



Theorem SatisfyImplicationCorrect:
    forall C1 C2,
        C1 satisfies C2 -> forall a, a elementOf C1 -> a elementOf C2.
Proof.
    intros C1 C2 H_sat. 
    induction H_sat; 
    intros a H_element;
    eauto using C_Satisfy_Rules, C_ElementOf_Rules;
    repeat match goal with 
    | IH: forall a, a elementOf ?C -> _, H: ?a elementOf ?C |- _ => 
        apply IH in H
    | H_element : ?a elementOf C_Constraint _ |- _ => inversion H_element; subst; clear H_element
    end;
    try solve[
        constructor;
        try assumption;
        try reflexivity;
        try unfold PrimLe in *;
        try unfold PrimGe in *;
        try unfold IsNumberType in *; 
        try solve[repeat (solve[left; auto] || right); auto]
    ];
    try match goal with 
    | |- ?a elementOf [- ?prop != ?b -] => 
        apply C_ElementOf_NotEqual;
        repeat match goal with 
        | b: bool |- _ => destruct b
        | prim: R_Lang_Primitive |- _ => destruct prim
        | |- ?a <> ?b => intros contra; inversion contra
        end;
        try (reflexivity || contradiction || discriminate || assumption)
    end;
    repeat match goal with 
    | H: ?C typedAs ?lst,
        H_elem: ?a elementOf ?C |- _ =>
        lazymatch goal with 
        | H: TypeInList lst (typeOfPrim a) |- _ => fail
        | |- _ => assert (TypeInList lst (typeOfPrim a)); 
            [apply (typing_matters C lst a); assumption |]
        end
    | H: TypeInList (single ?t) (typeOfPrim ?a) |- _ =>
        lazymatch goal with 
        | H0: typeOfPrim a = t |- _ => fail
        | |- _ => assert( typeOfPrim a = t);
            [simpl in H; destruct H; [rewrite H; reflexivity | contradiction] 
            | destruct a; try discriminate]
        end
    end;
    try solve[ apply IHH_sat1; inversion H_element; subst; assumption].
    - destruct b.
        + eapply C_ElementOf_Or_Left.
            * eapply C_TypesTo_Or.
                -- apply C_TypesTo_Equal.
                -- apply C_TypesTo_Equal.
            * simpl. left. reflexivity.
            * constructor.
        + eapply C_ElementOf_Or_Right.
            * eapply C_TypesTo_Or.
                -- apply C_TypesTo_Equal.
                -- apply C_TypesTo_Equal.
            * simpl. left. reflexivity.
            * constructor.
    - eapply C_ElementOf_Or_Left; [unifyAssumption | | unifyAssumption].
        inversion H; subst.

        


    repeat match goal with 
    | prim: R_Lang_Primitive |- _ => destruct prim; try contradiction
    end;
    try solve[apply IHH_sat1; assumption];
    try solve[apply IHH_sat2; assumption]; 
    
    try match goal with 
    | H: ?prim1 elementOf C_Constraint (_, (C_Op_LessThan, _)) |- _ =>
        tryif assert (IsNumberType prim1); [solve [auto]|] 
        then fail
        else solve [inversion H; contradiction]
    | H: ?prim1 elementOf C_Constraint (_, (C_Op_LessThanEqual, _)) |- _ =>
        tryif assert (IsNumberType prim1); [solve [auto]|] 
        then fail
        else solve [inversion H; contradiction]
    | H: ?prim1 elementOf C_Constraint (_, (C_Op_GreaterThan, _)) |- _ =>
        tryif assert (IsNumberType prim1); [solve [auto]|] 
        then fail
        else solve [inversion H; contradiction]
    | H: ?prim1 elementOf C_Constraint (_, (C_Op_GreaterThanEqual, _)) |- _ =>
        tryif assert (IsNumberType prim1); [solve [auto]|] 
        then fail
        else solve [inversion H; contradiction]
    end; 
    try match goal with 
    | H: _ \/ _ |- ?a elementOf [- ?C1 || ?C2 -] => 
        (solve [destruct H; [logicAuto_NoSpecialize; apply C_ElementOf_Or_Left; auto using C_ElementOf_Rules | 
            logicAuto_NoSpecialize; apply C_ElementOf_Or_Right; auto using C_ElementOf_Rules]] 
        || solve [destruct H; [logicAuto_NoSpecialize; apply C_ElementOf_Or_Right; auto using C_ElementOf_Rules | 
            logicAuto_NoSpecialize; apply C_ElementOf_Or_Left; auto using C_ElementOf_Rules]] 
        )
    end.
    - constructor.
        + intros contra; inversion contra; destruct b; discriminate.
        + reflexivity.  
    - destruct b. 
        + apply C_ElementOf_Or_Left. constructor.  
        + apply C_ElementOf_Or_Right. constructor.  
    - inversion H_element; subst; try solve [inversion H].
        + inversion H; subst.
        + destruct prim. inversion H_element; subst.  

    - constructor. unfold PrimLe in *. admit.
    - constructor. unfold PrimLe in *. admit.
    - inversion H2; inversion H3; subst. 
        constructor. unfold PrimLe in *. admit.
    - constructor. unfold PrimGe in *. admit.
    - constructor. unfold PrimLe in *. admit.
    - inversion H2; inversion H3; subst. 
        constructor. unfold PrimGe in *. admit.
Admitted.


Theorem SatisfyComplete:
    forall C1 C2,
    (exists elem, elem elementOf C1) -> 
    (forall a, a elementOf C1 -> a elementOf C2) -> C1 satisfies C2.
Proof.
    intros C1 C2 existential H.
    destruct existential as [elem H_element].
    remember H as H0; clear HeqH0.
    specialize (H0 elem H_element).
    induction H_element; induction H0; subst;
    try match goal with 
    | |- _ satisfies C_NoConstraint => apply C_Satisfies_Any
    end;
    try solve [ constructor ];
    try match goal with 
    | H: forall a, a elementOf ?C -> a elementOf [- self == ?prim -] |- _ =>
        let H0 := fresh "H" in 
        let a := fresh "a" in 
        assert (exists b, prim <> b) as H0; [
            apply primitives_have_opposites
            | 
            destruct H0 as [a H0];
            try solve[
                let H1 := fresh "H" in
                assert (a elementOf C) as H1;[
                    solve [eauto using C_ElementOf_Rules]
                    | 
                    apply H in H1;
                    inversion H1; subst;
                    contradiction
                ]
            ]
        ]
    | H: forall a, a elementOf ?C -> a elementOf [- self != ?prim -] |- _ =>
        let H0 := fresh "H" in 
        solve[
            assert (prim elementOf C) as H0; [
                eauto using C_ElementOf_Rules
                | apply H in H0; inversion H0; subst; contradiction
            ]
        ]
    |   H: forall a, a elementOf ?C -> a elementOf [- ?C1 && ?C2 -]
        |- _ =>
        let a := fresh "a" in 
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        assert ((forall a, a elementOf C -> a elementOf C1) /\ (forall a, a elementOf C -> a elementOf C2)) as H1;
        [ 
            split; intros a H1; apply H in H1; 
            inversion H1; subst; assumption
            | 
            destruct H1 as [H1 H2];
            try match goal with 
            |   IH1: (forall a : R_Lang_Primitive, a elementOf C -> a elementOf C1) -> C satisfies C1,
                IH2: (forall a : R_Lang_Primitive, a elementOf C -> a elementOf C2) -> C satisfies C2
                |- C satisfies [- C1 && C2 -] => 
                specialize (IH1 H1); specialize (IH2 H2);
                logicAuto;
                apply C_Satisfies_AndRight;
                assumption
            end
        ]
    end.
    - shelve.
    - shelve.
    - match goal with 
        | H: forall a, a elementOf ?C -> a elementOf [- self != ?prim -] |- _ =>
        let H0 := fresh "H" in 
        assert (prim elementOf C) as H0; [
            eauto using C_ElementOf_Rules
            | apply H in H0; inversion H0; subst; contradiction
        ]
    end. 
        
    - assert (exists b, a <> b); [apply primitives_have_opposites|].
        logicAuto. 
        satisfiesNoConstraint x.
        logicAuto.
        inversion H; subst.
        contradiction.
    - 
    - 

    
    assert (forall a,
        a elementOf C_NoConstraint -> a elementOf C1).
        + intros a0 H1. apply H in H1. inversion H1; subst. 
    - admit.
    - 

    - destruct elem. 


    
    specialize
    - admit.
    - apply C_Satisfies_AndRight. 

    induction C1; induction C2;
    
    - destruct s; destruct p; destruct c0;
        try match goal with 
        | H: forall a : R_Lang_Primitive,
            a elementOf C_NoConstraint ->
            a elementOf C_Constraint (_, (C_Op_NotEqual, ?r))|- _ =>
            let H0 := fresh "H" in 
            assert (r elementOf C_NoConstraint) as H0; [apply C_ElementOf_NoConstraint|];
            apply H in H0; inversion H0; contradiction
        end;
        destruct r; inversion C2_WellTyped;
        subst; try contradiction.
        + assert (R_Prim_Bool (negb b) elementOf C_NoConstraint);[apply C_ElementOf_NoConstraint|].
            apply H in H0. inversion H0; subst; destruct b; discriminate.
        + assert (R_Prim_Int (z + 1) elementOf C_NoConstraint);[apply C_ElementOf_NoConstraint|];
            apply H in H0; inversion H0; subst. admit.
        +  assert (R_Prim_Int (z + 1) elementOf C_NoConstraint);[apply C_ElementOf_NoConstraint|];
            apply H in H0; inversion H0; subst. unfold PrimLe in H4. admit.
        + clear H1. assert (R_Prim_Int (z + 1) elementOf C_NoConstraint);[apply C_ElementOf_NoConstraint|];
            apply H in H0; inversion H0; subst. destruct H6; [unfold PrimLe in H1 |]; admit.
        +  assert (R_Prim_Int (z - 1) elementOf C_NoConstraint);[apply C_ElementOf_NoConstraint|];
        apply H in H0; inversion H0; subst. unfold PrimGe in H4. admit.
        + clear H1. assert (R_Prim_Int (z - 1) elementOf C_NoConstraint);[apply C_ElementOf_NoConstraint|];
        apply H in H0; inversion H0; subst. destruct H6; [unfold PrimLe in H1 |]; admit.
    - inversion C2_WellTyped; subst. 
        specialize (IHC2_1 H2).  
        specialize (IHC2_2 H3).  
Qed.





























Inductive C_Equivalent_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=
| C_Equivalent_Exact: forall C,
    C_Equivalent_Rules C C

| C_Equivalent_AndComm: forall C C',
    C_Equivalent_Rules [- C && C' -] [- C' && C -]
| C_Equivalent_AndStep: forall C C' C'',
    C_Equivalent_Rules [- C -] [- C'' -] ->
    C_Equivalent_Rules [- C && C' -] [- C'' && C' -]
| C_Equivalent_AndAssoc1: forall C C' C'',
    C_Equivalent_Rules [- C && (C' && C'') -] [- (C && C') && C'' -]
| C_Equivalent_AndAssoc2: forall C C' C'',
    C_Equivalent_Rules [- (C && C') && C'' -] [- C && (C' && C'') -]
| C_Equivalent_AndSame1: forall C,
    C_Equivalent_Rules [- C -] [- C && C-]
| C_Equivalent_AndSame2: forall C,
    C_Equivalent_Rules [- C && C-] [- C -]
| C_Equivalent_AndNoConstraint1: forall C,
    C_Equivalent_Rules [- C && Any -] [- C -]
| C_Equivalent_AndNoConstraint2: forall C,
    C_Equivalent_Rules [- C -] [- C && Any -]

| C_Equivalent_OrComm: forall C C',
    C_Equivalent_Rules [- C || C' -] [- C' || C -]
| C_Equivalent_OrStep: forall C C' C'',
    C_Equivalent_Rules [- C -] [- C'' -] ->
    C_Equivalent_Rules [- C || C' -] [- C'' || C' -]
| C_Equivalent_OrAssoc1: forall C C' C'',
    C_Equivalent_Rules [- C || (C' || C'') -] [- (C || C') || C'' -]
| C_Equivalent_OrAssoc2: forall C C' C'',
    C_Equivalent_Rules [- (C || C') || C'' -] [- C || (C' || C'') -]
| C_Equivalent_OrSame1: forall C,
    C_Equivalent_Rules [- C -] [- C || C-]
| C_Equivalent_OrSame2: forall C,
    C_Equivalent_Rules [- C || C-] [- C -]
| C_Equivalent_OrNoConstraint1: forall C,
    C_Equivalent_Rules [- C || Any -] [- Any -]
| C_Equivalent_OrNoConstraint2: forall C,
    C_Equivalent_Rules [- Any -] [- C || Any -]

| C_Equivalent_Le1: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop <= prim -] [- prop < prim || prop == prim -]
| C_Equivalent_Le2: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop < prim || prop == prim -] [- prop <= prim -]
| C_Equivalent_Le3: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop < prim -] [- prop <= prim && prop != prim  -]
| C_Equivalent_Le4: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop <= prim && prop != prim -] [- prop < prim -]

| C_Equivalent_Ge1: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop >= prim -] [- prop > prim || prop == prim -]
| C_Equivalent_Ge2: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop > prim || prop == prim -] [- prop >= prim -]
| C_Equivalent_Ge3: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop > prim -] [- prop >= prim && prop != prim  -]
| C_Equivalent_Ge4: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop >= prim && prop != prim -] [- prop > prim -]

| C_Equivalent_CompNeq1: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop != prim -] [- prop > prim || prop < prim -]
| C_Equivalent_CompNeq2: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop > prim || prop < prim -] [- prop != prim -]

| C_Equivalent_CompEq1: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop == prim -] [- prop >= prim && prop <= prim -]
| C_Equivalent_CompEq2: forall prop prim,
    IsNumberType prim ->
    C_Equivalent_Rules [- prop >= prim && prop <= prim -] [- prop == prim -]



| C_Equivalent_BoolNeq1: forall prop b,
    C_Equivalent_Rules [- prop == (bool b) -] [- prop != (bool (negb b)) -]
| C_Equivalent_BoolNeq2: forall prop b,
    C_Equivalent_Rules [- prop != (bool (negb b)) -] [- prop == (bool b) -]

| C_Equivalent_BoolOr1: forall prop,
    C_Equivalent_Rules [- prop == true || prop == false -] [- Any -]
| C_Equivalent_BoolOr2: forall prop,
    C_Equivalent_Rules [- Any -] [- prop == true || prop == false -]



| C_Equivalent_LeInt1: forall prop z,
    C_Equivalent_Rules [- prop <= int z -] [- prop < int (Z.add z 1) -]
| C_Equivalent_LeInt2: forall prop z,
    C_Equivalent_Rules [- prop < int (Z.add z 1) -] [- prop <= int z -]

| C_Equivalent_GeInt1: forall prop z,
    C_Equivalent_Rules [- prop >= int z -] [- prop > int (Z.sub z 1) -]
| C_Equivalent_GeInt2: forall prop z,
    C_Equivalent_Rules [- prop > int (Z.sub z 1) -] [- prop >= int z -]
.

Ltac equivalenceConstructor :=
match goal with 
| |- C_Equivalent_Rules _ _ =>
    (solveWithConstructor C_Equivalent_Exact) ||
    (solveWithConstructor C_Equivalent_AndComm) ||
    (solveWithConstructor C_Equivalent_AndStep) ||
    (solveWithConstructor C_Equivalent_AndAssoc1) ||
    (solveWithConstructor C_Equivalent_AndAssoc2) ||
    (solveWithConstructor C_Equivalent_AndSame1) ||
    (solveWithConstructor C_Equivalent_AndSame2) ||
    (solveWithConstructor C_Equivalent_AndNoConstraint1) ||
    (solveWithConstructor C_Equivalent_AndNoConstraint2) ||
    (solveWithConstructor C_Equivalent_OrComm) ||
    (solveWithConstructor C_Equivalent_OrStep) ||
    (solveWithConstructor C_Equivalent_OrAssoc1) ||
    (solveWithConstructor C_Equivalent_OrAssoc2) ||
    (solveWithConstructor C_Equivalent_OrSame1) ||
    (solveWithConstructor C_Equivalent_OrSame2) ||
    (solveWithConstructor C_Equivalent_OrNoConstraint1) ||
    (solveWithConstructor C_Equivalent_OrNoConstraint2) ||
    (solveWithConstructor C_Equivalent_Le1) ||
    (solveWithConstructor C_Equivalent_Le2) ||
    (solveWithConstructor C_Equivalent_Le3) ||
    (solveWithConstructor C_Equivalent_Le4) ||
    (solveWithConstructor C_Equivalent_Ge1) ||
    (solveWithConstructor C_Equivalent_Ge2) ||
    (solveWithConstructor C_Equivalent_Ge3) ||
    (solveWithConstructor C_Equivalent_Ge4) ||
    (solveWithConstructor C_Equivalent_BoolNeq1) ||
    (solveWithConstructor C_Equivalent_BoolNeq2) ||
    (solveWithConstructor C_Equivalent_BoolOr1) ||
    (solveWithConstructor C_Equivalent_BoolOr2) ||
    (solveWithConstructor C_Equivalent_LeInt1) ||
    (solveWithConstructor C_Equivalent_LeInt2) ||
    (solveWithConstructor C_Equivalent_GeInt1) ||
    (solveWithConstructor C_Equivalent_GeInt2) ||
    (solveWithConstructor C_Equivalent_CompNeq1) ||
    (solveWithConstructor C_Equivalent_CompNeq2) ||
    (solveWithConstructor C_Equivalent_CompEq1) || 
    (solveWithConstructor C_Equivalent_CompEq2)
end.

Notation "c1 'equivalentTo' c2" := (plus C_Equivalent_Rules c1 c2) (at level 40).

Lemma equivalence_rules_commutative:
    forall C C',
    C_Equivalent_Rules C C' ->
    C_Equivalent_Rules C' C.
Proof.
    intros C C' H.
    induction H; subst;
    try equivalenceConstructor.
Qed.

Theorem equivalenceCommutative:
    forall C C',
    C equivalentTo C' ->
    C' equivalentTo C.
Proof.
    intros C C'.
    apply plus_relationCommute_plusCommute; clear C C'.
    apply equivalence_rules_commutative.
Qed.

Theorem equivalenceSubstitution:
    forall C C' Ce Ce',
    C equivalentTo Ce ->
    C' equivalentTo Ce' ->
    Ce equivalentTo Ce' ->
    C equivalentTo C'.
Proof.
    intros C C' Ce Ce' Equiv1 Equiv2 H.
    induction Equiv1; induction Equiv2; subst;
    logicAuto.
    - eapply plus_multi; [apply H0 | ]. 
        eapply plus_step_between; [unifyAssumption |].
        apply equivalence_rules_commutative. assumption.
    - eapply plus_step_between.
        + unifyAssumption.
        + apply equivalence_rules_commutative. assumption.
    - eapply plus_multi.
        + unifyAssumption.
        + assumption.
    -  eapply plus_multi.
        + unifyAssumption.
        + assumption.
Qed.




Reserved Notation "c1 'excludes' c2" (at level 40).
Inductive C_Exlusion_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=

| C_Excludes_ConstraintEquivalence: forall C C' Ce Ce',
    C equivalentTo Ce ->
    C' equivalentTo Ce' ->
    Ce excludes Ce' ->
    C excludes C'

| C_Excludes_AndRight: forall C C' C'',
    C excludes C' ->
    C excludes [- C' && C'' -]

| C_Excludes_AndLeft_Left: forall C C' C'',
    C excludes C'' ->
    [- C && C' -] excludes C''
| C_Excludes_AndLeft_Right: forall C C' C'',
    C' excludes C'' ->
    [- C && C' -] excludes C''

| C_Excludes_OrRight: forall C C' C'',
    C excludes C' -> 
    C excludes C'' ->
    C excludes [- C' || C'' -]
| C_Excludes_OrLeft: forall C C' C'',
    C excludes C'' -> 
    C' excludes C'' ->
    [- C || C' -] excludes C''


| C_Exludes_Eq_Neq: forall prop prim,
    [- prop == prim -] excludes [- prop != prim-]

| C_Exludes_Neq_Eq: forall prop prim,
    [- prop != prim -] excludes [- prop == prim-]

| C_Exludes_EqDiff: forall prop prim prim',
    prim <> prim' ->
    [- prop == prim -] excludes [- prop == prim'-]

| C_Excludes_LeGe: forall prop z z',
    z < z' ->
    [- prop <= int z -] excludes [- prop >= int z' -]
| C_Excludes_GeLe: forall prop z z',
    z > z' ->
    [- prop >= int z -] excludes [- prop <= int z' -]

| C_Excludes_LeEq: forall prop z z',
    z < z' ->
    [- prop <= int z -] excludes [- prop == int z' -]

| C_Excludes_EqLe: forall prop z z',
    z > z' ->
    [- prop == int z -] excludes [- prop <= int z' -]

| C_Excludes_GeEq: forall prop z z',
    z > z' ->
    [- prop >= int z -] excludes [- prop == int z' -]

| C_Excludes_EqGe: forall prop z z',
    z < z' ->
    [- prop == int z -] excludes [- prop >= int z' -]

where "c1 'excludes' c2" := (C_Exlusion_Rules c1 c2).

Ltac exclusionConstructors := 
match goal with 
| |- _ excludes _ =>
    (solveWithConstructor C_Exludes_Eq_Neq) ||
    (solveWithConstructor C_Exludes_Neq_Eq) ||
    (solveWithConstructor C_Exludes_EqDiff) ||
    (solveWithConstructor C_Excludes_LeGe) ||
    (solveWithConstructor C_Excludes_GeLe) ||
    (solveWithConstructor C_Excludes_LeEq) ||
    (solveWithConstructor C_Excludes_EqLe) ||
    (solveWithConstructor C_Excludes_GeEq) ||
    (solveWithConstructor C_Excludes_EqGe) ||
    (solveWithConstructor C_Excludes_ConstraintEquivalence) ||
    (solveWithConstructor C_Excludes_AndRight) ||
    (solveWithConstructor C_Excludes_AndLeft_Left) ||
    (solveWithConstructor C_Excludes_AndLeft_Right) ||
    (solveWithConstructor C_Excludes_OrRight) ||
    (solveWithConstructor C_Excludes_OrLeft)
end.



Theorem exclusionCommutative: 
    forall C C',
    C excludes C' ->
    C' excludes C. 
Proof.
    intros C C' H.
    induction H; subst;
    try flipRelations;
    try exclusionConstructors.
    - eapply C_Excludes_ConstraintEquivalence.
        + apply plus_one.
            apply C_Equivalent_Exact.
        + apply plus_one.
            apply C_Equivalent_AndComm.
        + exclusionConstructors.
    Admitted.



Inductive C_Satisfy_Rules: Constraints_Lang -> Constraints_Lang -> Prop :=

| C_Satisfy_Equal: forall C,
    C_Satisfy_Rules C C

| C_Satisfy_ConstraintEquivalence: forall C C' Cs Cs',
    C equivalentTo Cs ->
    C' equivalentTo Cs' ->
    C_Satisfy_Rules Cs Cs' ->
    C_Satisfy_Rules C C'

| C_Satisfy_NoConstraint: forall C ,
    C_Satisfy_Rules C [- Any -]

| C_Satisfy_AndRight: forall C C' C'',
    C_Satisfy_Rules C C' ->
    C_Satisfy_Rules C C'' ->
    C_Satisfy_Rules C [- C' && C'' -]
| C_Satisfy_AndLeft: forall C C' C'',
    C_Satisfy_Rules C C'' ->
    C_Satisfy_Rules [- C && C' -] C''

| C_Satisfy_AndSplit: forall C C' C'',
    C_Satisfy_Rules C [- C' && C'' -] ->
    C_Satisfy_Rules C C'



| C_Satisfy_OrRight: forall C C' C'',
    C_Satisfy_Rules C C' ->
    C_Satisfy_Rules C [- C' || C'' -]
| C_Satisfy_OrLeft: forall C C' C'',
    C_Satisfy_Rules C C'' ->
    C_Satisfy_Rules C' C'' ->
    C_Satisfy_Rules [- C || C' -] C''


| C_Satisfy_LeEqLeEq: forall z z' prop, 
    z <= z' ->
    C_Satisfy_Rules [- prop <= int z -] [- prop <= int z' -]

| C_Satisfy_GeEqGeEq: forall z z' prop, 
    z >= z' ->
    C_Satisfy_Rules [- prop >= int z -] [- prop >= int z' -]
.

Notation "c1 'satisfies' c2" := (plus C_Satisfy_Rules c1 c2) (at level 40).

Ltac satisfiesConstructors := 
match goal with 
| |- C_Satisfy_Rules _ _ =>
    (solveWithConstructor C_Satisfy_Equal) ||
    (solveWithConstructor C_Satisfy_NoConstraint) ||
    (solveWithConstructor C_Satisfy_ConstraintEquivalence) ||
    (solveWithConstructor C_Satisfy_AndRight) ||
    (solveWithConstructor C_Satisfy_AndLeft) ||
    (solveWithConstructor C_Satisfy_AndSplit) ||
    (solveWithConstructor C_Satisfy_OrRight) ||
    (solveWithConstructor C_Satisfy_OrLeft) ||
    (solveWithConstructor C_Satisfy_LeEqLeEq) ||
    (solveWithConstructor C_Satisfy_GeEqGeEq)
end.

Theorem satisfiesSubstitution:
    forall C C' Ce Ce',
    C equivalentTo Ce ->
    C' equivalentTo Ce' ->
    Ce satisfies Ce' ->
    C satisfies C'.
Proof.
    intros C C' Ce Ce' Equiv1 Equiv2 H.
    induction Equiv1; induction Equiv2; subst;
    logicAuto.
    - eapply plus_multi.
        +  eapply C_Satisfy_ConstraintEquivalence.
            * apply plus_one. unifyAssumption.
            * apply plus_one. apply C_Equivalent_Exact.
            * apply C_Satisfy_Equal.
        + eapply plus_step_between.
            * apply H.
            * eapply C_Satisfy_ConstraintEquivalence.
                -- apply plus_one. apply C_Equivalent_Exact.
                -- apply plus_one. unifyAssumption.
                -- apply C_Satisfy_Equal.   
    - eapply plus_step_between.
        + unifyAssumption.
        + eapply C_Satisfy_ConstraintEquivalence.
            * apply plus_one. apply C_Equivalent_Exact.
            * apply plus_one. unifyAssumption.
            * apply C_Satisfy_Equal. 
    - eapply plus_multi.
        + eapply C_Satisfy_ConstraintEquivalence.
            * apply plus_one. unifyAssumption.
            * apply plus_one. apply C_Equivalent_Exact.
            * apply C_Satisfy_Equal.
        + assumption.    
    - eapply plus_multi.
        + eapply C_Satisfy_ConstraintEquivalence.
            * apply plus_one. unifyAssumption.
            * apply plus_one. apply C_Equivalent_Exact.
            * apply C_Satisfy_Equal.
        + assumption.
Admitted. 



(* Facts about the relations that should hold *)

Theorem ExludeNotSatisfy:
    forall C C',
    C excludes C' ->
    ~ (C satisfies C').
Proof.
    intros C C' H. 
    induction H; subst;
    intros contra.

    - eapply satisfiesSubstitution in contra;[
        | apply equivalenceCommutative in H; apply H
        | apply equivalenceCommutative in H0; apply H0
    ]. 
    Admitted. (*assumption.
    - eapply invert_between in contra; logicAuto; [
        apply plus_one; satisfiesConstructors
        | eapply plus_step_between; [
            unifyAssumption
            | satisfiesConstructors
        ]
    ]. 
    - eapply invert_between in contra; 
    logicAuto; [ apply plus_one | eapply plus_step_between].
        + satisfiesConstructors. 
        destruct contra.
    
    
    unifyAssumption.
    try match goal with
    | Equiv1: ?C equivalentTo ?Ce,
        Equiv2: ?C' equivalentTo ?Ce',
        H: ?C satisfies ?C' |- _ => 
        notHypothesis (Ce satisfies Ce');
        apply equivalenceCommutative in Equiv1;
        apply equivalenceCommutative in Equiv2;
        let new := fresh "H" in
        (assert (Ce satisfies Ce') as new; 
        try solveWithConstructor C_Satisfy_ConstraintEquivalence);
        apply equivalenceCommutative in Equiv1;
        apply equivalenceCommutative in Equiv2
    end;
    try logicAuto;
    try contradiction.
    Admitted.
    *)


Theorem SatisfyNotExlude:
    forall C C',
    C satisfies C' ->
    ~ (C excludes C').
Proof.
    Admitted.


Theorem EquivNotExlude:
    forall C C',
    C equivalentTo C' ->
    ~ (C excludes C').
Proof.
    Admitted.

Theorem ExludeNotEquive:
    forall C C',
    C excludes C' ->
    ~ (C equivalentTo C').
Proof.
    Admitted.

Theorem EquivSatisfaction:
    forall C C',
    C equivalentTo C' <-> (C satisfies C' /\ C' satisfies C).
Proof.
    Admitted.
