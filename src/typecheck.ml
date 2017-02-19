open Printf
open Atom
open Types
open Equations
open Terms
open Symbols
open Print
open Typerr

(* ------------------------------------------------------------------------- *)

(* Specification of the type-checker. *)

(* The core of the typechecker is made up of two mutually recursive
   functions. [infer] infers a type and returns it; [check] infers a
   type, checks that it is equal to the expected type, and returns
   nothing. *)

(* The type [ty] that is produced by [infer] should be correct, that
   is, the typing judgement [hyps, tenv |- term : ty] should hold.
   Furthermore, it should be unique, that is, for every type [ty']
   such that the judgement [hyps, tenv |- term : ty'] holds, the
   hypotheses [hyps] entail the equation [ty = ty']. *)

(* The function [check] should be correct, that is, if it succeeds,
   then the typing judgement [hyps, tenv |- term : expected] holds. *)

(* ------------------------------------------------------------------------- *)

(* A completeness issue. *)

(* Ideally, the functions [infer] and [check] should be complete, that
   is, if they fail, then the term is ill-typed according to the
   typing rules in Pottier and Gauthier's paper. However, with the
   tools that we provide, this goal is difficult to meet, for the
   following reason.

   Consider, for instance, a function application [x1 x2]. We can use
   [infer] to obtain the types of [x1] and [x2], say, [ty1] and
   [ty2]. Then, we must check that, FOR SOME TYPE [ty], THE HYPOTHESES
   [hyps] ENTAIL THAT the type [ty1] is equal to the function type
   [TyArrow ty2 ty].

   This is a bit problematic. Of course, if the hypotheses [hyps] are
   empty, this is easy: it is just a syntactic check. If somehow the
   type [ty] was known, this would be easy as well: it would be an
   entailment check, for which we provide a decision procedure.
   However, in the general case, we need to solve a more difficult
   problem -- entailment with unknowns -- for which (out of laziness,
   perhaps) we haven't provided an algorithm.

   As a result, we suggest that you stick with a simple syntactic
   check. Your type-checker will thus be incomplete. That will not be
   a real problem: the user can work around it by adding an explicit
   type annotation to convert [ty1] into the desired function type
   [TyArrow ty1 ty]. The sample file [test/good/conversion.f]
   illustrates this.
   
   If you follow our suggestion and develop an incomplete
   type-checker, then you may run into a problem when implementing
   defunctionalization. The program produced by your
   defunctionalization phase may be well-typed, yet may be rejected by
   your type-checker, for the above reason. If this happens, you will
   have to work around the problem by having your defunctionalization
   algorithm produce explicit type annotations where appropriate. *)

(* ------------------------------------------------------------------------- *)

(* The type-checker. *)

let count = ref 0

let rec build_equations (hyps : equations) : ftype -> equations * ftype = function
  | TyWhere (t1, t2, t3) -> build_equations ((t2, t3) :: hyps) t1
  | t1 -> (hyps, t1)

let rec remove_forall (ty : ftype) (tyList : ftype list) : ftype =
  match ty, tyList with
  | TyForall context, hd :: tl -> remove_forall (fill context hd) tl
  | TyForall _, [] -> failwith "deu ruim"
  | _ , hd :: tl -> failwith "deu ruim"
  | t , [] -> t

let rec gen_fresh_vars l xenv = function
  | 0 ->
     (l, xenv)
  | n ->
     let at = Atom.fresh (Identifier.mk "var" Syntax.type_sort) in
     gen_fresh_vars ((TyFreeVar at) :: l) (Export.bind xenv at)(n - 1)
                
let rec fills xenv loc at type_abs types expected found =
  match types, type_abs with 
      | [], ty -> ty
      | hd :: tl, TyForall ctx -> fills xenv loc at (fill ctx hd) tl expected (found + 1)
      | _, _ -> arity_mismatch xenv loc "data constructor" at "type" expected found
           
let check_missing_clause
      (p : program)
      (xenv : Export.env) (*Original xenv*)
      (hyps : equations) (*Original equations*)
      (loc : Error.location) (* a location, for reporting errors; *)
      (at : Atom.atom)
      (ty2 : ftype list) (*types applied to constructor*)
    : unit =
  let tyScheme = type_scheme p at in
  let (types, xenv2) = gen_fresh_vars [] xenv (count_foralls tyScheme) in
  let instantiated_scheme = fills xenv loc at tyScheme types (List.length types) 1 in
  let (hyps2, ty) = build_equations hyps instantiated_scheme in
  let (domain, codomain) = deconstruct_arrow xenv loc ty in
  let types = deconstruct_tuple xenv loc domain in
  let (k, ty1) = deconstruct_tycon2 xenv loc codomain in
  let hyps2 = List.append (List.combine ty1 ty2) hyps in
  if not (inconsistent hyps2) then
    missing_clause xenv2 hyps2 loc at

let rec infer              (* [infer] expects... *)
    (p : program)          (* a program, which provides information about type & data constructors; *)
    (xenv : Export.env)    (* a pretty-printer environment, for printing types; *)
    (loc : Error.location) (* a location, for reporting errors; *)
    (hyps : equations)     (* a set of equality assumptions *)
    (tenv : tenv)          (* a typing environment; *)
    (term : fterm)         (* a term; *)
    : ftype =              (* ...and returns a type. *)
  
  match term with

  | TeVar (at) ->
     lookup at tenv
                         
  | TeAbs (at, type_domain, term_body, info) -> (*\lambda at : type_domain. term_body*)
     let type_image = infer p (Export.bind xenv at) loc hyps (bind at type_domain tenv) term_body in
     info := Some {hyps = hyps; tenv = tenv; fty = TyArrow (type_domain, type_image)};
     TyArrow (type_domain, type_image)
               
  | TeApp (t1, t2, info) -> (*t1 t2*)
     let type_arrow = infer p xenv loc hyps tenv t1 in
     let (domain, image) = deconstruct_arrow xenv loc type_arrow in
     check p xenv hyps tenv t2 domain;
     info := Some {domain = domain; codomain = image};
     image
                     
  | TeLet (at, t1, t2) -> (*let at = t1 in t2*)
     let ty1 = infer p (Export.bind xenv at) loc hyps tenv t1 in
     let ty2 = infer p (Export.bind xenv at) loc hyps (bind at ty1 tenv) t2 in
     ty2
     
  | TeFix (at, ty, t) -> (*fix at : ty . t *)
     check p (Export.bind xenv at) hyps (bind at ty tenv) t ty;
     ty

  | TeTyAbs (at, t1) -> (*\Lambda at. t1*)
     let type_body = infer p (Export.bind xenv at) loc hyps tenv t1 in
     TyForall (abstract at type_body)

  | TeTyApp (t, tau) -> (*t \tau*)
     let type_t = infer p xenv loc hyps tenv t in
     let context = deconstruct_univ xenv loc type_t in
     fill context tau
             
  | TeData (k, types, terms) -> (* k types terms*)
     let tyScheme = type_scheme p k in
     let type_no_quant = fills xenv loc k tyScheme types (List.length types) 1 in
     let (d, type_no_eqs) = build_equations [] type_no_quant in
     if entailment hyps d then
       let (domain, codomain) = deconstruct_arrow xenv loc type_no_eqs in
       let tuple = deconstruct_tuple xenv loc domain in
       let (atCons, listTy) = deconstruct_tycon2 xenv loc codomain in
       (*Need to verify if each term in "terms actually has the right types"*)
       if (List.length terms != List.length tuple) then
         arity_mismatch xenv loc "data constructor" k "term" (List.length tuple) (List.length terms)
       else
         List.map2 (fun x y -> check p xenv hyps tenv x y) terms tuple;
       (*If they don't have the same length, List.map2 will not work*)
       TyCon (atCons, listTy)
     else
       unsatisfied_equation xenv loc hyps (fst (List.hd d)) (snd (List.hd d));
       
  | TeTyAnnot (term, ty) ->
     (*print_string ("Annot: " ^ (print_type xenv ty) ^ "\n");*)
     check p xenv hyps tenv term ty;
     ty

  | TeMatch (term, ty, clauses) -> (*Match term of ty with clauses*)
     let type_domain = infer p xenv loc hyps tenv term in
     let (k, types) = deconstruct_tycon2 xenv loc type_domain in
     let dcs = ref (data_constructors p k) in
     (*By the end of this opeation, we need to verify if every remaining instance in dcs can't be
       instantiated under its hypothesis*)
     List.map (fun x -> check_clause p xenv hyps tenv k dcs ty types x) clauses;
     AtomSet.iter (fun x -> check_missing_clause p xenv hyps loc x types) !dcs;
     ty

  | TeLoc (location, t) ->
     infer p xenv location hyps tenv t
           
and check_clause
    (p : program)      
    (xenv : Export.env) (*Original xenv*)
    (hyps : equations) (*Original equations*)
    (tenv : tenv) (*Original environment*)
    (k_matched : Atom.atom) (*type constructor*)
    (dcs : AtomSet.t ref) (*data constructors associated with k_matched*)
    (expected : ftype) (*The type expected*)
    (ty2 : ftype list) (*types applied to constructor*)
    (clause : clause) (*Clause to have its type checked*)
    : unit =
  match clause with
  | Clause (PatData (loc, at, type_atoms, term_atoms), t) ->
     let Prog (_, _, dc) = p in
     let tyScheme = type_scheme p at in (*Type Scheme associated with the atom at*)
     let xenv2 = Export.sbind xenv type_atoms in
     let xenv2 = Export.sbind xenv2 term_atoms in (*extending the xenv with information in the pattern*)
     let types = List.map (fun x -> (TyFreeVar x)) type_atoms in (*Types applied in the pattern*)
     let instantiated_scheme = fills xenv loc at tyScheme types (List.length types) 1 in
     let (hyps2, ty) = build_equations hyps instantiated_scheme in
     let (domain, codomain) = deconstruct_arrow xenv loc ty in
     let types = deconstruct_tuple xenv loc domain in
     if List.length term_atoms != List.length types then
       arity_mismatch xenv loc "data constructor" at "type" (List.length types) (List.length term_atoms);
     let extended_env = List.combine term_atoms types in
     let tenv2 = binds extended_env tenv in
     let (k, ty1) = deconstruct_tycon2 xenv loc codomain in
     if not (Atom.equal k k_matched) then
       typecon_mismatch xenv loc at k_matched k;
     let hyps2 = List.append (List.combine ty1 ty2) hyps in
     if inconsistent hyps2 then
       inaccessible_clause loc;
     if AtomSet.mem at !dcs then
       (dcs := AtomSet.remove at !dcs;
        check p xenv2 hyps2 tenv2 t expected)
     else
       redundant_clause loc
                  
     
and check                  (* [check] expects... *)
    (p : program)          (* a program, which provides information about type & data constructors; *)
    (xenv : Export.env)    (* a pretty-printer environment, for printing types; *)
    (hyps : equations)     (* a set of equality assumptions *)
    (tenv : tenv)          (* a typing environment; *)
    (term : fterm)         (* a term; *)
    (expected : ftype)     (* an expected type; *)
    : unit =               (* ...and returns nothing. *)

  (* We bet that the term begins with a [TeLoc] constructor. This should be
     true because the parser inserts one such constructor between every two
     ordinary nodes. In fact, this is not quite true, because the parser
     sometimes expands syntactic sugar without creating intermediate [TeLoc]
     nodes. If you invoke [check] in reasonable places, it should just work. *)
  
  match term with
  | TeLoc (loc, term) ->
      let inferred = infer p xenv loc hyps tenv term in
      if entailment hyps [(inferred, expected)] then
        ()
      else
        mismatch xenv loc hyps expected inferred

  | _ ->
      (* out of luck! *)
      assert false

(* ------------------------------------------------------------------------- *)

(* A complete program is typechecked within empty environments. *)

let run (Prog (tctable, dctable, term) as p : program) =
  let xenv = Export.empty
  and loc = Error.dummy
  and hyps = []
  and tenv = Types.empty in
  let xenv = AtomMap.fold (fun tc _ xenv -> Export.bind xenv tc) tctable xenv in
  let xenv = AtomMap.fold (fun dc _ xenv -> Export.bind xenv dc) dctable xenv in
  xenv, infer p xenv loc hyps tenv term
