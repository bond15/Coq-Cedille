Require Import Template.All.
Require Import List String.
Load Cedille.


Inductive myNat : Type :=
|zz : myNat
|ss : myNat -> myNat.

Inductive ntree (A : Type) : Type :=
| leaf : (ntree A)
| node : A -> myNat -> (ntree A) -> (ntree A) -> (ntree A).

Fixpoint testfix (a : ntree nat) : myNat :=
  match a with
  | leaf _ => zz
  | node _  a n l r => n
  end.

Quote Recursively Definition rt := ntree.
Quote Recursively Definition rfix := testfix.
Print rt.

(* Definitions *)
Definition rTerm := prod global_declarations term.
Definition ctor  := (prod (prod ident term) nat).
Record env : Set := mkEnv { kername : string ; tyAndCtors : list (string * (list string)); lced : list ced }.

Definition emptyenv : env := mkEnv "empty" nil nil.

Definition setKername (e : env) (name : string ) : env :=
  match e with
  | {| kername:=k ; tyAndCtors:=xs ;  lced:=ys |} => mkEnv name nil ys 
  end.

Definition updateProg ( e : env) (c : ced ): env :=
  match e with
  | {| kername:=k ; tyAndCtors:=xs ;  lced:=ys |} => mkEnv k xs (cons c ys)
  end.

Definition updateTyAndCtors (e : env ) (x : string * (list string)) : env :=
  match e with
  | {| kername:=k ; tyAndCtors:=xs ;  lced:=ys |} => mkEnv k (cons x xs) ys
  end.


(* Helpers, Get methods *)
Definition getOneIndBody (t : mutual_inductive_body) := (head (t.(ind_bodies))).


(* Previous work----------------------- *)


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

Fixpoint Kind (t : term) : ced :=
  match t with
  | tProd _ _ (tSort _ ) => (arr (arr star star) star)
  | tProd _ _ rt => (arr (Kind rt) star)
  | _ => star
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

Definition TypeToFunctor (ts : list ctor) :=
  let pieces := map (fun c => (toFunctor (snd (fst c)) "ERROR NAME")) ts 
  in
  (replaceCarry (findCarry (glue pieces) "ERROR NAME")).


Fixpoint hbinders (t : term) (body : ced ): ced :=
  match t with
  | tProd (nNamed name) _ (tSort _) => pLambda name body  (* end *)
  | tProd (nNamed name) _ rt => pLambda name (hbinders rt body)
  | _ => body 
  end.

Definition binders (b : one_inductive_body ) : ced :=
  (hbinders b.(ind_type) (pLambda "R" (convertF (TypeToFunctor b.(ind_ctors))))).
  
(* ------------------------------------ *)

(*
 (* inject *)
 Definition inFunctor ( f : Functor ) : ced :=
   match f with
   | Prod l r => (tmApptm (tvar "in") (tmApptm (tvar "in2") (tmApptm (tvar "pair")
   end. 
   (tmApptm (tvar "in") (tmApptm (tvar "in1") (
                                           

 (* peel sum types *)
 Fixpoint smtc ( f : Functor  ) : list ced :=
   match f with
   | Sum l r => 
   | Prod l r => 
   | 
   end.
 
Definition tosmt (ts : list ctor)(e : env) :=
  let pieces := map (fun c => (pair (fst (fst c)) (toFunctor (snd (fst c)) "ERROR NAME"))) ts 
  in
  let strfun := map (fun c => (pair (fst c) (replaceCarry (findCarry (snd c) "ERROR NAME"))))  pieces
  in 
  let cnames := map fst strfun
  in (updateTyAndCtors e (pair e.(kername) cnames)).
 *)

Fixpoint asdf (t : term) : ced :=
  match t with
  | tProd (nNamed name) _ (tSort _) => (tvar name)
  | tProd (nNamed name) _  rt => (tyAppty (asdf rt) (tvar name))
  | _ => (tvar "ERROR")
  end.


Definition makeFunctor (b : one_inductive_body) ( e : env) : env :=
  (updateProg e (def ((b.(ind_name))++"F") (Kind b.(ind_type)) (binders b))).

Definition makeFixFunctor (b : one_inductive_body) (e : env) : env :=
  (updateProg e (def (b.(ind_name)) (Kind b.(ind_type)) (hbinders b.(ind_type) (tyAppty (tvar "FixM") (tyAppty (tvar (b.(ind_name)++"F")) (asdf b.(ind_type))))))).

Definition makeSmartCons (b : one_inductive_body) (e : env) : env :=
  e.


Definition processInductive (b : mutual_inductive_body)(e:env) :=
  match (getOneIndBody b) with
  | Some x => let e'  := (makeFunctor x e) in
              let e'' := (makeFixFunctor x e') in
              let e''':= (makeSmartCons x e'') in
              e'''
  | None => e
  end.
  

Definition processConstant (b : constant_body)(e:env) := e.





Definition processDecls' (decl : global_decl) (e : env) :  env :=
  match decl with
   | InductiveDecl kername mut_ind_body => (processInductive mut_ind_body (setKername e kername)) 
   | ConstantDecl kername body => (processConstant body (setKername e kername)) 
  end.


Fixpoint  processDecls (decls : list global_decl ) ( e : env) : env :=
  match decls with
  | nil => e
  | x::xs  => (processDecls xs (processDecls' x e))
  end.

Definition convert (r : rTerm) : env :=
  (processDecls (fst r) emptyenv).

Definition printAll (r : rTerm ) : list string :=
  map print (convert r).(lced).



Inductive fourc : Type :=
|c1 : fourc
|c2 : fourc -> fourc
|c3 : fourc -> fourc
|c4 : fourc -> fourc.
Quote Recursively Definition r := fourc.


Print rt.
Compute (convert r).
Compute (convert rt).
Compute (printAll rt).
Compute (convert rfix).
Compute (printAll rfix).

Print rfix.

Inductive testtype  (A B : Type ) ( a : A ) (b : A -> B) : Type := 
| cc1 : testtype A B a b .

Quote Recursively Definition rtt := testtype.
Print rtt.



