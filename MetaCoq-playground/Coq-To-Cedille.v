Require Import Template.All.
Require Import List String.


(* first approximation at getting constructors for 'simple' types and converting them to a functor represenation *)

Definition rTerm := prod global_declarations term.
Definition ctor := (prod (prod ident term) nat).

Definition getTypes (rt : rTerm) :=
  map (fun dec : global_decl =>
         match dec with
         |InductiveDecl ker mib => Some mib.(ind_bodies)
         | _ => None
         end) (fst rt).



Definition getSimpleType (rt : rTerm ) :=
  match (head (fst rt)) with
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



(* functor without constant *)

Inductive Functor : Type :=
| unit : Functor
| carry : Functor
| coprod : Functor -> Functor -> Functor
| prod : Functor -> Functor -> Functor
(* garbage *)
| empty : Functor.     


Fixpoint ctorToFunctor ( c : term ) :=
  match c with
  | tRel _ => unit
  | tProd _ _ (tRel _) => carry  
  | tProd _ _ r => (prod carry (ctorToFunctor r))
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

(* Examples *)

Inductive nat : Type :=
| z : nat
| s : nat -> nat.


Quote Recursively Definition rnat := nat.
Compute (simpleTypeToFunctor rnat).

(* Cedille Syntax - reference: cedille-1.0.0/core/Types.hs *)


Inductive pureTerm : Type :=
| pureVar : string -> pureTerm
| pureLambda : string -> pureTerm
| pureApp : pureTerm -> pureTerm.

Inductive primType {A : Type} ( tm : A) : Type :=
| TpVar : string -> primType tm
| TpLambda : string -> primTpKd tm -> primTpKd tm -> primType tm
| TpAll : string -> primTpKd tm -> primTpKd tm -> primType tm
| TpAppTp : primType tm -> primType tm -> primType tm
| TpAppTm : primType tm -> A -> primType tm
with primKind {A : Type} (tm : A) : Type :=
| Star : primKind tm
  with primTpKd {A : Type} (tm : A) : Type :=
| TpKdTp : primType tm -> primTpKd tm
| TpKdKd : primKind tm -> primTpKd tm.

Set Printing Universes.

(* cType := PrimType cTerm *)
Inductive cTerm : Type :=
| TmVar : string -> cTerm
| TmLambda : string -> primType cTerm -> cTerm -> cTerm.
| TmAppTm : cTerm -> cTerm -> cTerm.


Definition Command : Type :=  string -> cKind -> cType.  
