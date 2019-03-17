Require Import List Arith.
Require Import Template.All.
Import ListNotations MonadNotation.

Local Open Scope string_scope.

(** This is just printing **)
Test Quote (fun z x y : nat => z).

Print Quote.
Search "tInd".
Print term.
Print inductive.
Print kername.
Print universe_instance.
Print Instance.
Print mfixpoint.
Print def.
Print name.

Test Quote term.


Test Quote (fun (f : nat -> nat) (x : nat) => f x).


(* skeleton to  write a function that computes over term *)

(* base *)

Definition test (t : term) : bool :=
  match t with
  | tRel _ => true
  | tVar _ => true
  | tMeta _ => true
  | tEvar _ _ => true
  | tSort _ => true
  | tCast _ _ _  => true
  | tProd _ _ _  => true
  | tLambda _ _ _  => true
  | tLetIn _ _ _ _ => true
  | tApp _ _  => true
  | tConst _ _ => true
  | tInd _ _  => false
  | tConstruct _ _ _  => true
  | tCase _ _ _ _=> true
  | tProj _ _ => true
  | tFix _ _ => true
  | tCoFix _ _ => true
  end.



(* Define a basic inductive type with a simple functor signature *)
Inductive ty : Type :=
| c1 : ty
| c2 : ty -> ty
| c3 : ty -> ty -> ty.               

(* Get a reified term of this simple type *)

Print Build_one_inductive_entry. (* used to build inductive type from meta coq description *)


(* Quote vs Quote Recursively *)
Quote Definition n := Nat.add.
Print n.
Quote Recursively Definition n2 := Nat.add.
Print n2.
(*---*)



(* Getting the reified term of simple type ty *)

Quote Recursively Definition rty:= ty.
(* returns a product of (global_declarations * term *)
(* global_declarations is just list global_decl *)

Print rty.

(* Function to extract constructors from reified inductive type *)


Definition rTerm := prod global_declarations term.
Definition ctor := (prod (prod ident term) nat).




Inductive ty1 : Type :=
  |cc1 : ty1 -> ty1 -> ty1 -> ty1.

Quote Recursively Definition rty1 := ty1.
Print rty1.

Inductive t2 : Type :=
  |ccc1 : nat -> t2.

Quote Recursively Definition rt2 := t2.
Print rt2.


Inductive t3 : Type :=
  | cccc1 : ty -> t3.

Quote Recursively Definition rt3 := t3.
Print rt3.


Inductive t4 : Type :=
| cccccc1 : t2 -> t4.

Quote Recursively Definition rt4 := t4.
Print rt4.


Print rt4.



Fixpoint mylast {A : Type} ( xs : list A )  : option A :=
  match xs with
  | [] => None
  | x :: [] => Some x
  | x :: xs => mylast xs  
  end.

Print rty.
Print global_declarations.
Print global_decl.
Print mutual_inductive_body.
Print one_inductive_body.




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









(* example of inductive type for simple typed lambda calculus  syntax*)
Import String.

Inductive tm : Type :=
  (* lambda terms *)
  | tvar : string -> tm
  | tapp : tm -> tm -> tm
  | tabs : string -> ty -> tm -> tm
  (* base type terms *)
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.


Quote Recursively Definition rstlc := tm.
Compute (getTypes rstlc).


(* functor without constant *)

Inductive Functor : Type :=
| unit : Functor
| carry : Functor
| coprod : Functor -> Functor -> Functor
| prod : Functor -> Functor -> Functor
(* garbage *)
| empty : Functor.                                 



Inductive mnat : Type :=
| z : mnat
| sz : mnat -> mnat.


Quote Recursively Definition rmnat := mnat.
Compute (getSimpleCtors rmnat).

        
Fixpoint ctorToFunctor ( c : term ) :=
  match c with
  | tRel _ => unit
  | tProd _ _ (tRel _) => carry  
  | tProd _ _ r => (prod carry (ctorToFunctor r))
  | _ => empty                   
  end.


Fixpoint glue ( f : list Functor) : Functor :=
  match f with
  | [] => empty
  | x :: [] => x
  | x :: xs => (coprod x (glue xs))
  end.

Definition simpleTypeToFunctor (rt : rTerm) :=
  let pieces := map (fun c => ctorToFunctor (snd (fst c))) (getSimpleCtors rt)
  in
  glue pieces.


(* demo *)
Print mnat.
Print rmnat.
Compute (simpleTypeToFunctor rmnat).

Print ty.
Print rty.
Compute (simpleTypeToFunctor rty).

(* 'eats itself' *)
Quote Recursively Definition rFunctor := Functor.
Compute (simpleTypeToFunctor rFunctor).

(*------------------ *)
Inductive ty2 : Type :=
| d : ty2
| dd : ty2 -> ty2 -> ty2 -> ty2 -> ty2 -> ty2.

Quote Recursively Definition rty2 := ty2.
Print rty2.
Compute (simpleTypeToFunctor rty2).
(*--------------------*)


Quote Recursively Definition rplusO_n := plus_O_n.
Print rplusO_n.
(* to types with other types in constructors ... *)




             
Test Quote (let x := 2 in x).

Test Quote (let x := 2 in
            match x with
              | 0 => 0
              | S n => n
            end).

(** Build a definition **)
Definition d : Ast.term.
  let t := constr:(fun x : nat => x) in
  let k x := refine x in
  quote_term t k.
Defined.

Print d.

(** Another way **)
Quote Definition d' := (fun x : nat => x).

Print d.





(** To quote existing definitions **)
Definition id_nat : nat -> nat := fun x => x.

Quote Definition d'' := Eval compute in id_nat.

Print d''.

(** Fixpoints **)
Fixpoint add (a b : nat) : nat :=
  match a with
    | 0 => b
    | S a => S (add a b)
  end.
Eval vm_compute in add.

Fixpoint add' (a b : nat) : nat :=
  match b with
    | 0 => a
    | S b => S (add' a b)
  end.

Fixpoint even (a : nat) : bool :=
  match a with
    | 0 => true
    | S a => odd a
  end
with odd (a : nat) : bool :=
  match a with
    | 0 => false
    | S a => even a
  end.

