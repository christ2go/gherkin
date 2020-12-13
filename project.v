(*
  MATCH functions adapted from https://github.com/Lysxia/coq-ceres/tree/metacoq
 MIT License applies
 *)
Inductive Gentree (A: Type) :=
  Leaf: A -> Gentree A |
  Branch: nat -> list (Gentree A) -> Gentree A . 

Class Pickle (A : Type) :=
  pickle : A -> Gentree nat.

Class Unpickle (A : Type) :=
  unpickle : Gentree nat -> option A.

Require Import Coq.Arith.Peano_dec PeanoNat.
  
Require Import List Arith Ascii String Fin.
Require Import MetaCoq.Template.All.
Import ListNotations.
Set Universe Polymorphism.

Local Open Scope string_scope.


Notation TM := TemplateMonad.
Notation "x <- u ;; k" := (tmBind u (fun x => k))
  (at level 60, u at next level, right associativity) : template_scope.
Infix ">>=" := tmBind (at level 50, left associativity) : template_scope.
Notation "u ;; v" := (tmBind u (fun _ => v)) (at level 60, right associativity) : template_scope.
Delimit Scope template_scope with template.
Open Scope template_scope.

Notation tInd_ s := (tInd (mkInd s _) _).
Notation tCon_ s n := (tConstruct (mkInd s _) n _).


Inductive rtree := leaf: nat -> rtree
|                    z: option rtree -> rtree
|                    g: list nat -> rtree. 

(* MetaCoq Quote Definition qgentreeN := (Gentree nat). 
MetaCoq Quote Definition gentreeL := (Leaf nat 0).  *)

(* Get the [one_inductive_body] from a [mutual_inductive_body].
   Fails if there is more than one. *)
Definition get_ind_body (tyDef : mutual_inductive_body)
  : TemplateMonad one_inductive_body :=
  match ind_bodies tyDef with
  | [body] => tmReturn body
  | _ => tmFail "Unimplemented (mutually recursive types)"
  end.

Fixpoint annotateNums' {A: Type} (l : list A) (n: nat) : list (nat*A) :=
  match l with
    nil => nil
  | (x::xr) => (n, x)::(annotateNums' xr (S n)) end. 

Definition annotateNums {A: Type} (l :list A) : (list (nat*A)) := annotateNums' l 0.

Definition tmTraverse {A B} (f : A -> TemplateMonad B)
  : list A  -> TemplateMonad (list B) :=
  fix _traverse xs :=
    match xs with
    | [] => tmReturn []
    | x :: xs =>
      y <- f x ;;
      ys <- _traverse xs ;;
      tmReturn (y :: ys)
    end.

Definition when (b : bool) (u : TemplateMonad unit) : TemplateMonad unit :=
  if b then u else tmReturn tt.

Definition _tMatch
    (tyDef : mutual_inductive_body) (i : inductive) (ti : term) (ys : list term)
    (x : term) (z : term)
    (branch :  nat -> ident  -> context -> term -> TM term)
  : TM term :=
  tyBody <- get_ind_body tyDef ;;
  let params := firstn (ind_npars tyDef) ys in
  let tyBody' :=
    subst0 (rev' params) (remove_arity (ind_npars tyDef) (ind_type tyBody)) in
  let (ctx', ty0) := decompose_prod_assum [] tyBody' in
  let motive := it_mkLambda_or_LetIn ctx'
    (let n := List.length ctx' in
     tLambda
       nAnon
       (mkApps (lift0 n (tApp ti params)) (List.map tRel (rev' (seq 0 n))))
       (lift0 n z)) in
  let mkBranch : _ -> TM (nat * term) := fun ' (idx, (i, t, a)) =>
    let t'' := subst0 (rev' (ti :: params)) (remove_arity (ind_npars tyDef) t) in
    let '(ctx, t') := decompose_prod_assum [] t'' in
    tb <-   branch idx i ctx t' ;;
    tmPrint "Debug";;
    tmPrint i;;
    tmPrint a;;
    tmPrint t;;
    tmPrint ctx;;
    let u := it_mkLambda_or_LetIn ctx tb in
    tmReturn (a, u) in
  tmPrint "ctors";;
  tmPrint (ind_ctors tyBody);;
  branches <- tmTraverse mkBranch (annotateNums (ind_ctors tyBody)) ;;
  tmReturn (tCase (i, 0) motive x branches).

(* [match x : y return z with ... end]
   - [x]: Scrutinee
   - [y]: Type of scrutinee
   - [z]: "Motive", return type of the [match]
   - The [branch] function is given, for every branch, the name of the
     constructor, its fields as a [context], the result type of the
     constructor [term], and produces the [term] corresponding to the branch.
 *)
Definition tMatch
    (x : term) (y : term) (z : term)
    (branch : nat -> ident  -> context -> term -> TM term)
  : TM term :=
  let go i ti ys :=
    let name := inductive_mind i in
    tyDef <- tmQuoteInductive name ;;
    _tMatch tyDef i ti ys x z branch
  in
  match y with
  | tApp (tInd i _ as ti) ys => go i ti ys
  | tInd i _ as ti => go i ti []
  | _ => tmFail "Not matching an inductive"
  end.

Definition getName {A : Type} (a : A) : TM kername :=
  qa <- tmQuote a ;;
  match qa with
  | tConst name _ => tmReturn name
  | _ => tmFail "Not a constant"
  end.

Definition assert_else (b : bool) (s : string) : TM unit :=
  if b then tmReturn tt else tmFail s.

Definition isSortb : term -> bool := fun t =>
  match t with
  | tSort _ => true
  | _ => false
  end.
(** Define general trees **)

Print pickle. 
Print Pickle. 
MetaCoq Quote Definition qPickle := @Pickle.
Print qPickle. 
MetaCoq Quote Definition qpickle := @pickle.

MetaCoq Quote Definition qLeaf := @Leaf.
MetaCoq Quote Definition qLeafn := (@Leaf nat).

MetaCoq Quote Definition qGentree := @Gentree.
MetaCoq Quote Definition qGentreen := (@Gentree nat).

MetaCoq Quote Definition qOption := @option. 
Print qOption. 
Print qPickle. 

Definition tmInferInstanceQ
    (debug : bool) (rs : option reductionStrategy) (q_constraint : term)
  : TM term :=
  constraint <- tmUnquoteTyped Type q_constraint ;;
  tmPrint constraint ;;
      tmPrint ("Ceres: Searching for", constraint) ;;
  oinst <- tmInferInstance rs constraint ;;
  when debug (tmPrint oinst) ;;
  match oinst with
  | my_None =>
    tmFail "Instance not found"
  | my_Some inst => tmQuote inst
  end.

Fixpoint q_list_of_list_q (ty : term) (ts : list term) : term :=
  match ts with
  | [] => mkApp <%@nil%> ty
  | t :: ts => mkApps <%@cons%> [ty ; t ; q_list_of_list_q ty ts]
  end. 
MetaCoq Quote Definition qs := S.
MetaCoq Quote Definition qz := 0.

Fixpoint quoteNumber (n: nat) := match n with 0 => qz
                                       | (S n) => (mkApp qs (quoteNumber n)) end.
Check list nat. 
Definition pickleConstr
    (ctx : context) (n: nat) (cname : ident) (cfields : context) (_ : term)
  : TM term :=
  let ctx0 := ctx ,,, cfields in
  let n0 := List.length ctx0 in
  (* Loop to serialize each field. *)
  let fix pickleFields acc cfields' cn' :=
      match cfields' with
      | {| decl_type := t0;
           decl_name := dnn             
        |} :: ct2 =>
        if isSortb t0 then
          (* Don't try to serialize types. *)
          pickleFields acc ct2 (S cn')
        else ( 
          (* Run instance resolution for every field. *)
            let t1 := lift0 (S cn') t0 in

            let q_constraint :=
            it_mkProd_or_LetIn ctx0 (mkApp qPickle t1) in
          q_inst <- tmInferInstanceQ true None q_constraint ;;
          let q_inst' := mkApps q_inst (List.map tRel (rev' (seq 0 n0))) in
          let t := mkApps qpickle [t1; q_inst' ; tRel cn'] in
         tmPrint t0;; tmPrint "^ was ind ";; tmPrint dnn;;pickleFields (t :: acc) ct2 (S cn')
(*
          let q_constraint :=
              it_mkProd_or_LetIn ctx0 (mkApp <% Pickle %> t1)  in
          q_inst <- tmInferInstanceQ true None q_constraint ;; 
          let q_inst' := mkApps q_inst (List.map tRel (rev' (seq 0 n0))) in 

          print_nf ("Ceres: Quoted constraint", q_constraint);;
          let t := mkApps <% @pickle %> [t1 ; q_inst' ; tRel cn'] in 
          tmPrint "debufgggg ";;
          tmPrint q_constraint;; serializeFields (t :: acc) ct2 (S cn')*)
       )
      | [] => tmReturn acc
      end in
  pfields <-   pickleFields [] cfields 0  ;;
  q_cname <- tmQuote (cname) ;;
  tmPrint "==>";;
  tmPrint pfields;;
  (* tmEval lazy cfields >>= tmPrint ;; *)
  
   match pfields with
    | [] => (mkApps <% Branch nat %> [(quoteNumber n);  <%@nil (Gentree nat)%>])
    | _ :: _ => (mkApp (mkApp <% Branch nat %> (quoteNumber n)) (q_list_of_list_q <% @Gentree nat %> pfields)) 
    end. 


Definition _derivePickle
   (tyDef : mutual_inductive_body)
    (ctx : context) (q_PA' q_A : term)
  : TM term :=
    let name_sexp_of := nNamed "pickle" in
    let ctx' := ctx ,, vass name_sexp_of q_PA' ,, vass nAnon (lift0 1 q_A) in
    body <- tMatch (tRel 0) (lift0 2 q_A) qGentreen (pickleConstr ctx') ;;
    let body :=
      tFix [mkdef _ name_sexp_of (tProd nAnon q_A qGentreen )
                  (tLambda nAnon (lift0 1 q_A) body )  0] 0 in
    tmReturn (it_mkLambda_or_LetIn ctx body).
From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Definition mk_instance_name := fun s => "Pickle_" ++ s.
Check Gentree.
Check when. 
Definition derivePickleWith (SA : Type) (debug: bool) : TM unit :=
  q_SA <- tmQuote SA ;;
  let '(ctx, q_SA') := decompose_prod_assum [] q_SA in
  q_A <- match q_SA' with
    | tApp (tConst name _) [a] =>
      (* assert_else (eq_string name name_Serialize) 
        ("Ceres: Expected Serialize at the head, found " (* ++ name *));; *)
      tmReturn a 
    | q =>
      tmReturn q_SA';;
               tmFail "Ceres: Expected Serialize at the head"
    end ;;
  match q_A with
  | tInd i _ | tApp (tInd i _) _ =>
    tyDef <- tmQuoteInductive (inductive_mind i) ;;
    tyOne <- get_ind_body tyDef ;;
    q_body <- _derivePickle tyDef ctx q_SA' q_A ;;
    tmEval cbn q_body >>= tmPrint;;
    when debug (
               body <- tmUnquoteTyped (SA) q_body  >>= tmEval cbn >>= tmEval lazy ;; 
    iname <- tmEval all (mk_instance_name (ind_name tyOne))  ;; 
      tmDefinitionRed iname None body ;; 
     (* tmExistingInstance (ConstRef (nNamed iname));;  *)
    tmPrint body;; 
    tmReturn tt)  (*
    res' <- tmEval cbn (my_projT2 body) ;;
    tmDefinition "def" res';;
    tmReturn tt     );;
    tmPrint "Sucess" *)
  | Q =>
    tmPrint ("Pickle: Bad type", Q) ;;
    tmFail "Pckle: Not an inductive type"
  end.

Definition derivePickle : Type -> TM unit := fun A => (derivePickleWith A true).
Inductive test:= inda: nat -> nat -> nat -> nat -> test.  
Inductive form := Var: nat -> form | Imp: form -> form -> form | And: form -> form -> form | Or: form -> form | Bot: form.
MetaCoq Run  (derivePickle ( (Pickle nat))).
Inductive exp : Type -> Type := bexp (b : bool) : exp bool | uexp : exp unit.
MetaCoq Run  (derivePickle (forall A, Pickle bool -> Pickle (exp unit) -> (Pickle (exp A) ))).

Print Pickle_nat.
(*
MetaCoq Run  (derivePickle (Pickle nat -> (Pickle form))).
Print Pickle_form. 
Print term.  
MetaCoq Run  (derivePickle ((forall A B, Pickle A -> Pickle B -> (Pickle (sum A B))))).
MetaCoq Run (derivePickle (forall A, Pickle A -> Pickle (list A))).
MetaCoq Run (derivePickle (forall A B, Pickle A -> Pickle B -> Pickle (A*B))). 
MetaCoq Run (derivePickle (forall A, Pickle (A) -> Pickle (option (A)))). 
*)

(** 
    * UNPICKLE
    *
**)
Check isSort.


(**
   Unpickeling
 **)

(* Define a translation table used for storing already unpickled references *)
Print global_reference.
Require Import MetaCoq.Checker.Checker.
Print eq_term. 
Print name. 
Print global_reference.
Existing Instance config.default_checker_flags.

Definition tsl_table := list (global_reference * term).
Fixpoint lookup_tsl_table (E : tsl_table) t
  : option term :=
  match E with
  | nil => None
  | hd :: tl =>
    if gref_eq_dec (fst hd) t then Some (snd hd)
    else lookup_tsl_table tl t
  end.
Check tCase.
Print get_ind_body.

Definition get_ind_bodyOption (tyDef : mutual_inductive_body)
  : option one_inductive_body :=
  match ind_bodies tyDef with
  | [body] => Some body
  | _ => None
  end.
Print global_reference.
Definition UnpickleTbl : tsl_table := [].
Print global_reference. 
Definition tMatchl
    (tyDef : mutual_inductive_body) (i : inductive) (ti : term) (ys : list term)
    (x : term) (z : term) (table: tsl_table)
    (branch : tsl_table ->  nat -> ident  -> context -> term -> TM term)
    :=
  let tyBodyOpt := get_ind_bodyOption tyDef in
  match tyBodyOpt with None => tmFail "er"
                  |
                  Some a =>
                  (let tyBody := a in
                   let params := firstn (ind_npars tyDef) ys in
                   let indi := i in
  let tyBody' :=
    subst0 (rev' params) (remove_arity (ind_npars tyDef) (ind_type tyBody)) in
  let (ctx', ty0) := decompose_prod_assum [] tyBody' in
  
  let mkBranch : _ ->
                 TM (nat * term) := (fun ' (idx, (i, t, a)) =>
                                 let t'' := subst0 (rev' (ti :: params)) (remove_arity (ind_npars tyDef) t) in
                                 let '(ctx, t') := decompose_prod_assum [] t'' in
                                  u <-  (branch ((IndRef indi, (tRel 3))::table)  idx i ctx t' );;
                                 tmReturn (a, u))
  in
  
  z <- (tmTraverse mkBranch (annotateNums (ind_ctors tyBody)));;
  tmReturn z                 )
  end.
Check tMatchl. 

Print context_decl .
Print global_reference. 

(**
   Declare a function to get the constructor number from gentree nat
 **)

Definition getGTNList (T: Gentree nat) :=
  match T with
  | Branch x y => y
  | Leaf x => [] end.

Definition getCNum (T: Gentree nat) :=
  match T with
  | Branch x y => x
  | Leaf x => x end.

Print tCase.

Definition matchOption (t: option (Gentree nat)) :=
  match t with
    Some (Branch 1 xr) => 2 | _ => 3 end.
MetaCoq Quote Definition d := Eval cbv in  matchOption.
Print d.
Check List.nth.

Fixpoint  getNthOption  (n: nat) (l: list (Gentree nat))  :=
  match (l, n) with
    (x::xr, 0) => Some x
  | (x::xr, S n) => getNthOption n xr
  | _ => None
end.           
Check IndRef.
Print context_decl.
Print global_reference.
Search "global_reference".

Inductive isConstant : term -> Type :=
| constIsConstant s univs: isConstant (tConst s univs)
| indIsConstant i univs: isConstant (tInd i univs)
| constructIsConstant i n univs: isConstant (tConstruct i n univs).
Hint Constructors isConstant.

Definition getRef (t:term) {h:isConstant t} : global_reference.
inversion h.
- exact (ConstRef s).
- exact (IndRef i).
- exact (ConstructRef i n).
Defined.
Print tInd_.
Print tInd.
Definition isLeaf (a: Gentree nat) :=
  match a with
    Leaf _ => Some 12
  | _ => None end.
Definition optionify (A B: Type) (f: A -> option B) (g: option A) :  option B :=
  match g with
    Some a => (f a)
  | None => None end.

Check (@unpickle nat). 

Fixpoint unpickleGen
         (ctx0: context)
         (finishedArgs: list term) (* *)
         (idx: nat) (* Current position in constructor list *)

         (table: tsl_table) (* unpickle table (to check what to unpickle with *)
         (n: nat) (* Number this constructor has *)
         (cname : ident) (* Name for this ctor *)
         (cfields : context) (* Constructor list *)
         (t2 : term)
          : TM term                
 :=
    match cfields with
      nil =>
         (* Generate matches on unpickle of the fields (tRel 0), (tRel 1), (tRel 2) ,etc ...  *)
      tmPrint "Done for";;
      tmPrint cname ;;
      tmReturn  <%  @Some (nat) 12 %> (* Get arguments and *)
    | x::ct2 => (match x with
              | {|
                   decl_type := t0           
                |}  =>
                   (* Lookup the unpickle function for this argument *)
                let t1 := lift0 (
                              (S(idx)+3)) t0 in tmPrint "t1 is" ;; tmEval cbn t1 >>= tmPrint;;

            let q_constraint :=
             it_mkProd_or_LetIn ctx0  (mkApp <% @Unpickle %> t1) in
          q_inst <- tmInferInstanceQ true None q_constraint ;;
          let q_inst' := mkApps q_inst (List.map tRel (rev' (* (seq 0 (3+idx)) *) [0;2] )) in
          let t := mkApps <% @unpickle %> [t1; q_inst'] in

             rest <- unpickleGen  ctx0 finishedArgs (S idx) table n cname ct2 t2;;
               
             let xa :=
                 (mkApps <% optionify (Gentree nat) nat %> [
                           (* f: Gentree nat -> option nat *)
                           t;
                           (mkApps <% getNthOption %> [(quoteNumber idx); (mkApps <% getGTNList %> [(tRel 1)])])
                         ]) in   
                      
                   tmReturn  (tCase ({|
      inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "option");
      inductive_ind := 0 |}, 1)
                                   (tLambda nAnon
                                            <% option (nat) %> 
                                            <%  option nat  %>)
                                 (*  ) *) (* TODO: Pass correct option type *)
                          xa
                          [
                            (0, (tLambda nAnon <%  nat %> rest));
                            (1, <% @None (nat) %>)

                            (*(1,  <%(fun (z: Gentree nat) => @None (nat)) %> (* (tLambda nAnon <% Gentree nat %> <% @None nat %>) *))  (* <% fun (z: Gentree nat) => @None (nat) %> ) *) *)
                   ]) 
               (* Call unpickle with List.get  *)
               (* Generate case statement *)

               end)
    end 
.
Check tCase. 
(* [match x : y return z with ... end]
   - [x]: Scrutinee
   - [y]: Type of scrutinee
   - [z]: "Motive", return type of the [match]
   - The [branch] function is given, for every branch, the name of the
     constructor, its fields as a [context], the result type of the
     constructor [term], and produces the [term] corresponding to the branch.
 *)

Print tCase.
Definition t (n : nat) :=
  match n with
    0 => true |
  _ => false
  end.
MetaCoq Quote Definition vdef := Eval cbv in t.
Print vdef.
Check mkInd. 
Compute (List.nth 10 [1;2;3;4] 6).

Fixpoint getZeroArg {B: Type} (A: list (nat * B)) :=
  match A with
    nil => None
  | (0, b)::xr => Some b
  | x::xr => getZeroArg xr end. 
(** 
    Takes a list of pairs of nat and B, 
    deletes every pair with number 0 and decrements the other numbers.
**)
Fixpoint reduceArguments {B: Type} (A: list (nat * B)) :=
  match A with
    nil => nil
  | (S r, b)::xr => (r, b)::(reduceArguments xr)
  | x::xr => reduceArguments xr end.
Print kername.
Print tCase. 
Fixpoint natSimpleMatch
           (x: term) (* Natural number to match on *)
           (z: term) (* Return type *)
           (l: list (nat * term)) (* List of number -> return type *)
           (default: term)
           (fuel: nat)
  : term :=
    match fuel with 0 => default | S fuel' =>
    let cur := getZeroArg l in
    let rec := reduceArguments l in
    let rc := natSimpleMatch (tRel 0) z rec default fuel'  in 
     tCase ((mkInd ((MPfile ["Datatypes"; "Init"; "Coq"],
                        "nat"))) 0, 0) (tLambda nAnon <% nat %> z) x [(0, match cur with (Some y) => y | _ => default end); (1,(tLambda nAnon <% nat %> rc))] end. 



Definition constructorFields
    (tyDef : mutual_inductive_body) 
   :=
     let tyBodyO := get_ind_bodyOption tyDef in
     match tyBodyO with None => None | Some tyBody =>
 Some (annotateNums (ind_ctors tyBody)) end. 
MetaCoq Quote Definition qm := Eval hnf in nat. 
Print qm.

Check List.nth.

Definition tMatchl'
    (x : term) (y : term) (z : term) (table: tsl_table)
    (branch :tsl_table -> nat -> ident  -> context -> term -> TM term)
  : TM (list (nat * term)) :=
  let go i ti ys :=
    let name := inductive_mind i in
    tyDef <- tmQuoteInductive name ;;
    z <-  (tMatchl tyDef i ti ys x z table branch);;
  tmReturn z in 
  match y with
  | tApp (tInd i _ as ti) ys =>  x <- go i ti ys;; tmReturn  x
  | tInd i _ as ti => x <-  (go i ti []);; tmReturn x 
  | _ => tmFail "Not matching an inductive"
  end.

Fixpoint teOptionfy {T: Type} (l: list (nat * option T)) :=
  match l with
    nil => nil
  | ((a, Some b)::xr) => (a,b)::(teOptionfy xr)
  | x::xr => (teOptionfy xr) end. 

Definition _deriveUnpickle
   (tyDef : mutual_inductive_body)
    (ctx : context) (q_PA' q_A : term)
  : TM term :=
  let name_unpickle_of := nNamed "unpickle" in
  
    let ctx' := ctx ,, vass name_unpickle_of q_PA' ,, vass nAnon (lift0 1 q_A) in
   test <-
   tMatchl' (lift0 2 q_A) q_A <% option nat %> [] (unpickleGen ctx' [] 0) ;;
       tmPrint "test";;

       let t := (natSimpleMatch (tApp <% getCNum %> [(tRel 0)] ) (tApp qOption [q_A]) test ((tApp <% @None %> [q_A])) 10 ) in
    let body := tFix [mkdef _ name_unpickle_of (tProd nAnon qGentreen (tApp qOption [q_A]) )  (tLambda nAnon (lift0 1 qGentreen) t )  0] 0 in 
   
    tmPrint "ok";;
    let y :=  (it_mkLambda_or_LetIn ctx body) in 
    tmEval lazy y >>= tmPrint;;
    tmReturn y  .


Definition mk_instance_nameUP := fun s => "Unpickle_" ++ s.

Definition deriveUnpickleWith (SA : Type) (debug: bool) : TM unit :=
  q_SA <- tmQuote SA ;;
  let '(ctx, q_SA') := decompose_prod_assum [] q_SA in
  q_A <- match q_SA' with
    | tApp (tConst name _) [a] =>
      (* assert_else (eq_string name name_Serialize) 
        ("Ceres: Expected Serialize at the head, found " (* ++ name *));; *)
      tmReturn a 
    | q =>
      tmReturn q_SA';;
               tmFail "Ceres: Expected Serialize at the head"
    end ;;
  match q_A with
  | tInd i _ | tApp (tInd i _) _ =>
    tyDef <- tmQuoteInductive (inductive_mind i) ;;
    tyOne <- get_ind_body tyDef ;;
    q_body <- _deriveUnpickle tyDef ctx q_SA' q_A ;;
    (*tmEval cbn q_body >>= tmEval cbv >>= tmPrint;;*)
    when debug (
               body <- tmUnquoteTyped (SA) q_body  >>= tmEval cbn >>= tmEval lazy ;; 
    iname <- tmEval all (mk_instance_nameUP (ind_name tyOne))  ;; 
      tmDefinitionRed iname None body ;; 
     (* tmExistingInstance (ConstRef (nNamed iname));;  *)
    tmPrint body;; 
    tmReturn tt)  (*
    res' <- tmEval cbn (my_projT2 body) ;;
    tmDefinition "def" res';;
    tmReturn tt     );;
    tmPrint "Sucess" *)
  | Q =>
    tmPrint ("Pickle: Bad type", Q) ;;
    tmFail "Pckle: Not an inductive type"
  end.
Check List.nth.
Unset Strict Unquote Universe Mode.
Fixpoint Unpickle_natH (T: option (Gentree nat)): bool :=
  match T with
  (*  (Leaf 0) => Some 0 *)
  | Some _ => true
  | _ => false                    
  end.                                   
MetaCoq Quote Definition upnh := Eval cbv in  Unpickle_natH.
MetaCoq Unquote Definition upn := upnh.
Print upn. 
Print upnh. 
Inductive un := testUn: un -> un. 
MetaCoq Run (deriveUnpickleWith (Unpickle nat) false).
MetaCoq Run (deriveUnpickleWith (Unpickle nat) true).

Print Unpickle_nat.
Compute (Unpickle_nat (Pickle_nat 2)). 
MetaCoq Run (deriveUnpickleWith (Unpickle nat) false).

MetaCoq Run (deriveUnpickleWith (Unpickle nat) true).

MetaCoq Run (deriveUnpickleWith (forall A,(Unpickle (option A))) true). 

Compute (Unpickle_nat (Leaf nat 2)).
Print Unpickle_nat. 
From MetaCoq Require Import All.
Require Import MetaCoq.Template.All.
Check Gentree.
Check when. 


Print Pickle_sum. 
Print Pickle_nat.
Inductive pfree : Type :=
  | p0 : pfree
  | p1 : pfree
  | p2 (n:nat) : pfree
  | p3 : pfree -> pfree
  | p4 (b:bool) (p:pfree) (n:nat) : pfree.
MetaCoq Run  (derivePickle (Pickle nat -> Pickle bool -> (Pickle pfree))).

Inductive mlBin:= binLeaf: nat ->  mlBin | binTree: (mlBin*mlBin) -> mlBin.  
MetaCoq Run  (derivePickle ((Pickle nat) -> (Pickle (mlBin*mlBin) -> Pickle mlBin))).
Fixpoint pickleMlBin (b: mlBin) :Gentree nat :=
    (match b with
     | binLeaf x => Branch nat 0 [Pickle_nat x]
     | binTree x => let pickleP (x1: (mlBin * mlBin)) :=
                       (match x1 with
                        |(a,b)       => Branch nat 0 [pickleMlBin a; pickleMlBin b]
                        end)
                         
                   in Branch nat 1 [pickleP x] 
     end) 
  .       
       
Lemma pickleUnpickleCancel: forall (n: nat), (Unpickle_nat (Pickle_nat n)) = (Some n).
Proof.
  intro.
  induction n.
  -  reflexivity.
  - simpl Pickle_nat.   simpl Unpickle_nat.  rewrite IHn. reflexivity.
Qed.

Lemma pickle_inj (a b: nat) : Pickle_nat a = Pickle_nat b -> a = b.
Proof.
  intro H.
  apply (f_equal (Unpickle_nat)) in H.
  repeat rewrite pickleUnpickleCancel in H.
  inversion H. auto.
Qed.

Print pickleUnpickleCancel.
Print pickle_inj. 
Print Pickle_list. 
Compute (Pickle_nat 12).
Compute (Pickle_form Pickle_nat (Imp (Var 10) (Var 5))).
Print Pickle_form. 
   
Definition hv : Pickle nat := fix _pickle (H : nat) : Gentree nat :=
    match H with
    | 0 => Leaf nat 0
    | S _ => Leaf nat 1
    end.
Definition hvt : (nat -> Gentree nat) := fix _pickle (H : nat) : Gentree nat :=
    match H with
    | 0 => Leaf nat 0
    | S _ => Leaf nat 1
    end.

MetaCoq Quote Definition v := Eval cbv in hv.
MetaCoq Quote Definition v' := Eval cbv in hvt.
Print v.
Print v'.
(*
Definition fprim : (Pickle nat) -> (Pickle form). 
  intro.
  intro v.
  induction v.
  - apply (Branch nat 0 [(X n)]).
  - apply (Branch nat 1 [IHv1; IHv2]).
  -   
Defined.
Print fprim.
MetaCoq Quote Definition p :=  Eval cbv in fprim.
Print p. 

*)
(* MetaCoq Run  (deriveSerialize ((Pickle nat))). *)

Metacoq Run  (deriveSerialize ( (Pickle nat) -> (Pickle form))).
Print def. 
Check def.

Check pickle. 
Fixpoint pickle_nat (n: nat) :=
  match n with
    0 => (Leaf nat 0)
  | (S n) => (Leaf nat 0) end.
Print pickle_nat.
MetaCoq Quote Definition p :=  Eval cbv in pickle_nat.
Print p. 
Print def. 
Compute (def 4). 

Definition v := fix _pickle (H : nat) : Gentree nat := Leaf nat 0.
Check v.
MetaCoq Quote Definition dpn :=  (fix pickle_nat (n : nat) : Gentree nat := Leaf nat 0). 
Print dpn. 

Print qgentreeN. 
