Require Import Bool ZArith.


Inductive Primitive_Lang : Type :=
| R_Int: Z -> Primitive_Lang
| R_Bool: bool -> Primitive_Lang
.

Inductive Refinery_Lang : Type :=
| R_Primitive: Primitive_Lang -> Refinery_Lang
.

