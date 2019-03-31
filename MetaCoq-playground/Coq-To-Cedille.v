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
| ncons : nat -> natList -> natList.

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






(* adding single parameter polymorphic types *)

Inductive natMaybe : Type :=
| some : nat -> natMaybe
| none : natMaybe.

Inductive Maybe ( A : Type ) : Type :=
| some_a : A -> A -> A -> (Maybe A)
| no_a : (Maybe A).

Inductive Which ( A B C : Type ) : Type :=
| cc : A -> B -> C -> A -> B -> C -> B-> (Which A B C).

Quote Recursively Definition rnm := natMaybe.
Quote Recursively Definition rm  := Maybe.
Quote Recursively Definition mm  := Which.

Print mm.
Print rnm.
Print rm.
Print one_inductive_body.

Compute (getSimpleType rm).
Compute (getSimpleCtors rm).

Fixpoint toFunctor ( t : term) : Functor :=
  match t with
  | tProd (nNamed _) (tSort _) (tApp _ _) => unit  
  | tProd (nNamed _) (tSort _) r => (toFunctor r)  
  | tProd nAnon (tRel _) (tApp _ _) => (prod (const "A") carry)
  | tProd nAnon (tRel _) r => (prod (const "A") (toFunctor r))                                      
  | _ => empty
  end.

Definition TypeToFunctor (t : rTerm) :=
  let pieces := map (fun c => toFunctor (snd (fst c))) (getSimpleCtors t)
  in
  glue pieces.

Fixpoint TypeToCedille ( r : rTerm ) : string :=
  (print (def ((getName r)++"F")  (arr (arr star star) star) (tLambda "A" star (tLambda "R" star  (convertF (TypeToFunctor r)))))).


Compute (TypeToFunctor rm).
Compute (TypeToCedille rm).

Inductive mlist (A : Type) : Type :=
| n : (mlist A)
| c : A -> (mlist A) -> (mlist A).

Quote Recursively Definition rmlist := mlist.

Compute (TypeToCedille rmlist).

(* broken *)
Inductive tree (A : Type) : Type :=
| leaf : (tree A)
| node : A -> (tree A) -> (tree A) -> (tree A).

Quote Recursively Definition rtree := tree.

Compute (TypeToCedille rtree).