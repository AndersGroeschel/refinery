Require Import ZArith Bool.

Inductive Property_Logic: Type :=
| PL_self: Property_Logic
| PL_number: Z -> Property_Logic
| PL_true: Property_Logic
| PL_false: Property_Logic
| PL_equal: Property_Logic -> Property_Logic -> Property_Logic
.

(* need some way of computing whether or not a property is weaker or equivalent to another*)

(* need a way to manipulate properties based on operations*)

