Require Import Template.All.
Require Import List String.
Load Cedille.

(* first approximation at getting constructors for 'simple' types and converting them to a functor represenation *)

Definition rTerm := prod global_declarations term.
Definition ctor := (prod (prod ident term) nat).

(* a dummy global declaration used as the default value of the list last function *)
Definition dummy : global_decl := ConstantDecl "" {|cst_type:= (tRel 0); cst_body := None; cst_universes := Monomorphic_ctx (UContext.make nil ConstraintSet.empty) |}.


Definition getTypes (rt : rTerm) : list (option (list one_inductive_body))  :=
  map (fun dec : global_decl =>
         match dec with
         |InductiveDecl ker mib => Some mib.(ind_bodies)
         | _ => None
         end) (fst rt).

Definition getLastDecl (rt : rTerm) :=
  Some (last (fst rt) dummy).

Definition getLastType (rt : rTerm) : option (list one_inductive_body) :=
  (last (getTypes rt) None).

Definition getSimpleType (rt : rTerm ) :=
(* match (head (fst rt)) with *)
  match (getLastDecl rt ) with
  | Some (InductiveDecl ker mib) =>
    match (head mib.(ind_bodies)) with
    | Some indbody => Some indbody
    | _ => None
    end
  | _ => None
  end.

Definition getSimpleCtors (rt : rTerm) :=
  match (getSimpleType rt) with
  | Some indbody => indbody.(ind_ctors)
  | _ => nil
  end.


Inductive Functor : Type :=
| unit : Functor
| carry : Functor
| coprod : Functor -> Functor -> Functor
| prod : Functor -> Functor -> Functor
| const : string -> Functor
(* garbage *)
| empty : Functor.    


Fixpoint ctorToFunctor ( c : term ) :=
  match c with
  | tRel _ => unit
  | tProd _ (tInd t _ ) (tRel _ ) => (const t.(inductive_mind))              
  | tProd _ (tRel _) (tRel _) => carry
  | tProd _ (tInd t _) r => (prod (const t.(inductive_mind)) (ctorToFunctor r))
  | tProd _ (tRel _ ) r => (prod carry (ctorToFunctor r))
  | _ => empty
  end.

Fixpoint glue ( f : list Functor) : Functor :=
  match f with
  | nil => empty
  | x :: nil => x
  | x :: xs => (coprod x (glue xs))
  end.

Definition simpleTypeToFunctor (rt : rTerm) :=
  let pieces := map (fun c => ctorToFunctor (snd (fst c))) (getSimpleCtors rt)
  in
  glue pieces.
                            
Fixpoint convertF ( f : Functor ) : ced :=
  match f with
  | unit => (tvar "Unit")
  | carry => (tvar "R")
  | const str => (tvar str)             
  | coprod t1 t2 => (tyAppty (tyAppty (tvar "Sum") (convertF t1)) (convertF t2))
  | prod t1 t2 => (tyAppty (tyAppty (tvar "Product") (convertF t1)) (convertF t2))
  | _  => star                  
  end.

Definition getName (r : rTerm) : string:=
  match (getSimpleType r) with
  | Some body => body.(ind_name)
  | None => "error"              
  end.


Fixpoint simpleTypeToCedille ( r : rTerm ) : string :=
  (print (def ((getName r)++"F")  (arr star star) (tLambda "R" star  (convertF (simpleTypeToFunctor r))))).


(* examples *)

(*Nat*)
Inductive nat : Type :=
| z : nat
| s : nat -> nat.

Quote Recursively Definition rnat := nat.

Compute (simpleTypeToCedille rnat).


(* nat list *)
Inductive natList : Type :=
| nil : natList
| ncons : natList -> nat -> natList.

Quote Recursively Definition rnatList := natList.

Compute (simpleTypeToCedille rnatList).

(* nat tree *)
Inductive natTree : Type :=
| nleaf : natTree
| nnonde : natTree -> nat -> natTree -> natTree.

Quote Recursively Definition rnatTree := natTree.

Compute (simpleTypeToCedille rnatTree).

(* untyped lambda calculus *)
Inductive ulc : Type :=
| vars : string -> ulc
| lambda : string -> ulc -> ulc
| app : ulc -> ulc -> ulc.                              

Quote Recursively Definition rulc := ulc.

Compute (simpleTypeToCedille rulc).

