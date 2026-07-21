From stdpp Require Export ssreflect.

(** Iris itself and many dependencies still rely on this coercion. *)
Coercion Z.of_nat : nat >-> Z.
