Require Import Template.All.
Require Import List String.
Load Cedille.

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

Fixpoint glue ( f : list Functor) : Functor :=
  match f with
  | nil => empty
  | x :: nil => x
  | x :: xs => (coprod x (glue xs))
  end.
                            
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


Definition total_map (A : Type)  := Datatypes.nat -> A.
Definition t_empty { A : Type } ( v : A ) : total_map A :=
  (fun _ => v).
Definition t_update { A: Type } ( m : total_map A) (n : Datatypes.nat) (v : A) :=
  (fun n' =>  if (Nat.eqb n n') then v else m n').



Fixpoint hToFunctor (t : term ) (n : Datatypes.nat) (m : total_map ident) : Functor :=
  match t with
  (*map  lookups *)
  | (tRel n') => (const (m (n-n'-1)))
  | (tApp (tRel n') _ ) => (const (m (n-n'-1))) (* todo: specific type application *)
  | (tApp (tInd ind _ ) _) => (const ind.(inductive_mind))
  | (tInd ind _ ) => (const ind.(inductive_mind)) 
  (* insert to map *)
  | tProd (nNamed tyname) (tSort _) rt => (hToFunctor rt (n+1) (t_update m n tyname))

  (* recursively process *)
  | tProd _ rt1 rt2 => (prod (hToFunctor rt1 n m) (hToFunctor rt2 (n+1) m))

  (* error *)                       
  | _ => empty
  end.

Definition toFunctor (t : term ) (name : ident) : Functor :=
  (hToFunctor t 1 (t_update (t_empty "NULL") 0 name)).

(* looks for the carrier type in const *)
Fixpoint findCarry (f : Functor) (name : string ) : Functor :=
  match f with
  | const n => if (eq_string n name) then carry else (const n)
  | coprod t rt => (coprod (findCarry t name) (findCarry rt name))
  | prod t rt => (prod (findCarry t name) (findCarry rt name))
  | unit => unit
  | carry => carry
  | empty => empty
  end.

Fixpoint replaceCarry (f : Functor ) : Functor :=
  match f with
  | prod t carry => t
  | prod t rt => (prod t (replaceCarry rt))
  | coprod carry rt => coprod unit (replaceCarry rt)
  | coprod t rt => coprod t (replaceCarry rt)
  | const n => const n
  | unit => unit
  | carry => carry
  | empty => empty
  end.

Definition TypeToFunctor (t : rTerm) :=
  let pieces := map (fun c => (toFunctor (snd (fst c)) (getName t))) (getSimpleCtors t)
  in
  (replaceCarry (findCarry (glue pieces) (getName t))).


Fixpoint hbinders (t : term) (body : ced ): ced :=
  match t with
  | tProd (nNamed name) _ (tSort _) => pLambda name body  (* end *)
  | tProd (nNamed name) _ rt => pLambda name (hbinders rt body)
  | _ => star 
  end.

Definition binders (rt :rTerm ) : ced :=
  match (getSimpleType rt) with
  | Some t =>  (hbinders t.(ind_type) (pLambda "R" (convertF (TypeToFunctor rt))))
  | None => star
  end.

Fixpoint hKind (t : term) : ced :=
  match t with
  | tProd _ _ (tSort _ ) => (arr (arr star star) star)
  | tProd _ _ rt => (arr (hKind rt) star)
  | _ => star
  end.

Definition Kind (rt : rTerm ) : ced :=
  match (getSimpleType rt) with
  | Some t => (hKind t.(ind_type))
  | None => star
  end.


Definition TypeToCedille ( r : rTerm ) : string :=
  (print (def ((getName r)++"F") (Kind r)  (binders r))).




(* examples *)

Inductive mlist (A : Type) : Type :=
| n : (mlist A)
| cn : A -> (mlist A) -> (mlist A).

Quote Recursively Definition rmlist := mlist.

Print rmlist.
Compute (getSimpleType rmlist).
Compute (TypeToFunctor rmlist).
Compute (TypeToCedille rmlist).


Inductive tree (A : Type) : Type :=
| leaf : (tree A)
| node : A -> (tree A) -> (tree A) -> (tree A).

Quote Recursively Definition rtree := tree.

Compute (TypeToFunctor rtree).
Compute (TypeToCedille rtree).

