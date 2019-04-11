Require Import Template.All.
Require Import List String.
Load Cedille.

Definition rTerm := prod global_declarations term.
Definition ctor := (prod (prod ident term) nat).



Fixpoint Error (t : term) :ced :=
  match t with
  | (tConstruct _ _ _) => (tvar "ERROR -tConstruct")
  | (tConst _ _ ) => (tvar "ERROR -tConst")
  | (tInd _ _) => (tvar "ERROR -tInd")
  | (tRel _) => (tvar "ERROR -tRel")
  | (tVar _ ) => (tvar "ERROR-tVar")                          
  | (tMeta _ ) => (tvar "ERROR -tMeta")
  | (tEvar _ _ ) => (tvar "ERROR -tEvar")
  | (tSort _ ) => (tvar "ERROR -tSort")
  | (tCast _ _ _ ) => (tvar "ERROR -tCast")
  | (tProd _ _ _) => (tvar "ERROR -tProd")                     
  | (Ast.tLambda _ _ _) => (tvar "ERROR -tLambda")
  | (tLetIn _ _ _ _) => (tvar "ERROR -tLetIn")
  | (tApp _ _) => (tvar "ERROR -tApp")
  | (tCase _ _ _ _) => (tvar "ERROR -tCase")
  | (tProj _ _ ) => (tvar "ERROR -tProj")
  | (tFix _ _) => (tvar "ERROR -tFix")
  | (tCoFix _ _) => (tvar "ERROR -tCoFix")
  end.


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

(* TODO : add fixpoint and smart constructors *)
Definition TypeToCedille ( r : rTerm ) :=
  let functor := (def ((getName r)++"F") (Kind r)  (binders r)) in
  (*let fixfunctor := *)
  (*smart constructors*)
  print functor.





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


(* Algebras *)



Fixpoint evenb (n : Datatypes.nat) : bool :=
  match n with
  | S n' => negb (evenb n')
  | O => true
  end.

Quote Recursively Definition re := evenb.

Definition getFix (r : rTerm) :=
  match (getLastDecl r) with
  | Some (ConstantDecl _ t ) => t.(cst_body)
  | _ => None
  end.

Definition getFixBody (r : rTerm) :=
  match (getFix r) with
  | Some (tFix tm  _)  => match head tm with
                          | Some rec => Some rec.(dbody)
                          | _ => None
                          end
  | _ => None
  end.

Fixpoint rindexmap (t : term) (n : nat) (m : total_map ident) :=
  match t with
  | (Ast.tLambda (nNamed name) _ (tCase _ _ _ _)) => pair (t_update m n name) (n+1)
  | (Ast.tLambda (nNamed name) _ rt ) =>  (rindexmap rt (n+1) (t_update m n name)) 
  | _ => pair m n
  end.


Definition indexmap (r : rTerm) :=
  match (getFixBody r) with
  | Some x => (rindexmap x 1 (t_update (t_empty "ERROR -index map") 0 "function_Name"))
  | _ => pair (t_empty "ERROR") 0
  end.

(* TODO : recursive function calls replaced with rec *)                          

Fixpoint getFixCases' (t : term) :=
  match t with
  | (Ast.tLambda _ _ (tCase _ _ _ c)) => Some c
  | (Ast.tLambda _ _ rt) => (getFixCases' rt)
  | _ => None
  end.

Definition getFixCases (r : rTerm) :=
  match (getFixBody r) with
  | Some x =>
    match (getFixCases' x) with
    | Some xs => xs
    | _ => nil
    end
  | _ => nil
  end.



Fixpoint findConstructors (str : string) (l : list global_decl) :=
  let ct := (fun t =>  match head t with
                      | Some t => t.(ind_ctors)
                      | None => nil
                       end ) in
  match l with
  | (InductiveDecl name t)::xs => if (eq_string name str) then (ct t.(ind_bodies)) else (findConstructors str xs)
  | _ => nil
  end.

Definition d : ctor  := pair (pair "t" (tRel 0)) 0.


Definition findConstructor (n:nat)(str : string) (r : rTerm) :=
   (fst (fst (nth n (findConstructors str (fst r)) d))).



Print ced.
Fixpoint processAppList (l : list term) (n : nat) (m : total_map ident) : ced :=
  let f := (fun x => match x with
                     | (tRel x) => (tvar (m(n-x-1)))
                     | (tConstruct t n' _) => (tvar (findConstructor n' t.(inductive_mind) re))
                     | (tInd t _) => (tvar t.(inductive_mind))
                     | _ => (tvar "ERROR papplist")
                     end) in
  match l with
  | x :: nil => f x 
  | x :: xs => (tAppt (f x) (processAppList xs n m))
  | _ => (tvar "ERROR -app list")
  end.


Fixpoint parseCase (t : term)(n : nat)(m : total_map ident) : ced :=
  match t with
  | (Ast.tLambda (nNamed name) _ rt) => (plambda name (parseCase rt (n+1) (t_update m n name)))
  | (tApp t1 (t2::xs)) => (tAppt (parseCase t1 n m) (processAppList (t2::xs) n m))
  | (tInd t _ ) => (tvar t.(inductive_mind))
  | (tRel x) => (tvar (m(n-x-1)))
  | (tConst x _ ) => (tvar x)
  | (tConstruct t n' _) => (tvar (findConstructor n' t.(inductive_mind) re))
  (* *)
  | _ => (tvar "ERROR parseCase")
  end.

Quote Recursively Definition radd := Nat.add.


Definition toCed (r : rTerm) :=
  let start_map := (fst (indexmap r)) in
  let start_index := (snd (indexmap r)) in 
  let cases := (getFixCases r) in
  map (fun c => (parseCase (snd c) start_index start_map)) cases.

Compute (toCed radd).

(*
body...
tFix 
dname = evenb
dtype = nat -> bool
dbody = Ast.tLambda 
          name = n
          term1 = tInd .. nat
          term2 = tCase
                    Inductive * nat = (nat , 0) 
                    term = Ast.tLambda
                             name = n
                             term = tInd nat
                             term = tInd bool
                    term = tRel 0 --- n
                    List(nat * term) =
                              (0, tConstruct ( bool, 0 , nil)) --- nat for which constructor?
                              (1, Ast.tLambda 
                                    name = n'
                                    term = tInd nat
                                    term = tApp 
                                              tConst negb
                                              tApp
                                                 tRel 2 --- evenb
                                                 tRel 0 --- n'
 *)
Print tConstruct. (* inductive -> nat -> universe_instance -> term *)
Print Ast.tLambda. (* name -> term -> term -> term *)
Print tCase. (* inductive * nat -> term -> term -> list (nat * term) -> term *)
Print tFix. (* mfixpoint term -> nat -> term *)
Print mfixpoint. (* term => list (Ast.def term) *)
Print Ast.def. (* Record   {dname, dtype, dbody, rarg} *)