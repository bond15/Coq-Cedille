Require Import String.



(* Cedille Syntax - reference: cedille-1.0.0/core/Types.hs *)
Definition s_star : string := "★".
Definition s_asgn : string := "◂".
Definition s_arr  : string := "➔".
Definition s_lam  : string := "λ".
Definition s_Lam  : string := "Λ".
Definition s_all  : string := "∀".
Definition s_dot  : string := "·".
Definition s_eq   : string := " = ".
Definition s_spc  : string := " ".

Inductive ced : Type :=
| def : string -> ced -> ced -> ced
| star : ced
| arr : ced -> ced -> ced
| tLambda : string -> ced -> ced -> ced
| tvar : string -> ced
| tAppt : ced -> ced -> ced                     
| tyAppty : ced -> ced -> ced                     
| plambda : string -> ced -> ced
| pLambda : string -> ced -> ced
| tAll : string -> ced -> ced -> ced.

Definition program := list ced.


Fixpoint print( t : ced) : string :=
  match t with
  | def str kty tyterm => str ++ s_spc ++  s_asgn ++ s_spc  ++ (print kty) ++ s_eq ++ (print tyterm) ++ "."
  | star => s_star
  | arr l r => (print l) ++ s_spc ++ s_arr ++ s_spc ++ (print r)
  | tLambda str k b => s_lam ++ s_spc ++ str ++ " : " ++ (print k) ++ ". " ++ (print b)
  | tvar x => x
  | plambda str b => s_lam ++ s_spc ++ str ++ ". " ++ (print b)
  | pLambda str b => s_Lam ++ s_spc ++ str ++ ". " ++ (print b)
  | tyAppty l r => "(" ++ (print l) ++ s_dot ++ (print r) ++ ")"
  | tAppt l r => "(" ++ (print l) ++ s_spc ++ (print r) ++ ")"
  | tAll str k b => s_all ++ s_spc ++ str ++ " : " ++ (print k) ++ ". " ++ (print b)
  end.

(* examples *)
Definition Nat : ced :=
  (def "Nat" star (tyAppty (tvar "FixM") (tvar "NatF"))).

Compute (print Nat).

Definition FixM : ced :=
  (def "FixM" (arr (arr star star) star) (tLambda "F" (arr star star) (tAll "X" star (arr (tyAppty (tyAppty (tvar "AlgM") (tvar "F")) (tvar "X")) (tvar "X"))))).

Compute (print FixM).

Definition foldM : ced :=
  (def "foldM" (tAll "F" (arr star star) (tAll "X" star (arr (arr (tyAppty ( tyAppty (tvar "AlgM") (tvar "F")) (tvar "X")) (tyAppty (tvar "FixM") (tvar "F"))) (tvar "X")))) (pLambda "F" (pLambda "X" (plambda "alg" (plambda "d" (tAppt (tvar "d") (tvar "alg"))))))).

Compute (print foldM).

Definition In : ced :=
  (def "in" (tAll "F" (arr star star) (arr (tyAppty (tvar "F") (tyAppty (tvar "FixM") (tvar "F"))) (tyAppty (tvar "FixM") (tvar "F")))) (pLambda "F" (plambda "d" (pLambda "X" (plambda "alg"
   (tAppt (tAppt (tyAppty (tvar "alg") (tyAppty (tvar "FixM") (tvar "F"))) (tAppt (tvar "foldM") (tvar "alg"))) (tvar "d"))))))).

Compute (print In).

(* TODO add AlgM *)
Search list.
Definition cedilleMendlerFramework : program  := (cons FixM (cons foldM (cons In nil))).

Fixpoint printProgram (p : program) : string :=
  match p with
  | cons x xs => (print x)++"  " ++ (printProgram xs)
  | nil => ""
  end.

Compute (printProgram cedilleMendlerFramework).
                                          