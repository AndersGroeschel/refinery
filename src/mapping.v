Require Import List.

Definition partialMapping {A B: Type} := ((list ((A*B)%type)) * (A -> A -> bool))%type.

Definition lookup {A B: Type} (map: (partialMapping)) (key : A): option B :=
    let (list, equiv) := map in
    let fix look list :=  
        match list with 
        | (k,v)::rest => if (equiv key k) 
            then Some v 
            else look rest
        | nil => None
        end
    in
    look list.

    
Definition update {A B: Type} (map: partialMapping) (key: A) (value: B) := 
    let (list, equiv) := map in
     ((key,value)::list ,equiv).
