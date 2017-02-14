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
           
           
let rec infer              (* [infer] expects... *)
    (p : program)          (* a program, which provides information about type & data constructors; *)
    (xenv : Export.env)    (* a pretty-printer environment, for printing types; *)
    (loc : Error.location) (* a location, for reporting errors; *)
    (hyps : equations)     (* a set of equality assumptions *)
    (tenv : tenv)          (* a typing environment; *)
    (term : fterm)         (* a term; *)
    : ftype =              (* ...and returns a type. *)
  
  match term with

  | TeVar (at) -> lookup at tenv
                         
  | TeAbs (at, type_domain, term_body, info) ->
     let type_image = infer p (Export.bind xenv at) loc hyps (bind at type_domain tenv) term_body in
     TyArrow (type_domain, type_image)
               
  | TeApp (t1, t2, info) ->
     let type_arrow = infer p xenv loc hyps tenv t1 in
     let (domain, image) = deconstruct_arrow xenv loc type_arrow in
     let type_domain' = infer p xenv loc hyps tenv t2 in
     (if equal domain type_domain' then
        image
     else
       failwith "Does not typecheck! (App)")

  | TeLet (at, t1, t2) ->
     let ty1 = infer p (Export.bind xenv at) loc hyps tenv t1 in
     let ty2 = infer p (Export.bind xenv at) loc hyps (bind at ty1 tenv) t2 in
     ty2
     
  | TeFix  (at, ty, t) ->
     let ty1 = infer p (Export.bind xenv at) loc hyps (bind at ty tenv) t in
     if equal ty1 ty then
       ty1
     else
       failwith "Does not typecheck (TeFix)"
                                   
  | TeTyAbs (at, t1) ->
     (*Add var freshness to it*)
     let ty = infer p (Export.bind xenv at) loc hyps tenv t1 in
     TyForall (abstract at ty)

  | TeTyApp (t, ty) ->
     let ty1 = infer p xenv loc hyps tenv t in
     (match ty1 with
      | TyForall (context) ->
         fill context ty
              
      | _ -> failwith "Does not typecheck (TeTyApp)")
       
              
  | TeData (at, tys, terms) ->
     let tyScheme = type_scheme p at in
     let ty1 = remove_forall tyScheme tys in
     let (d, ty2) = build_equations [] ty1 in
     print_string ("Esquema: " ^ (print_type xenv tyScheme) ^ "\n");
     if entailment hyps d then
       (match ty2 with
        | TyArrow ((TyTuple tuple), (TyCon (atCons, listTy))) ->
           List.map2 (fun x y -> check p xenv hyps tenv x y) terms tuple;
           (*Need to verify if each term in "terms actually has the right types"*)
           TyCon (atCons, listTy)
        | _ -> failwith "Wrong type scheme")
     else
       failwith "Equations do not entail"
       
  | TeTyAnnot (t, ty) ->
     let ty' = infer p xenv loc hyps tenv t in
     (*print_string ("Annot: " ^ (print_type xenv ty) ^ "\n");*)
     ty
                           
  | TeMatch (t, ty, clauses) ->
   
     let ty1 = infer p xenv loc hyps tenv t in
     (*    let ty2 = infer_clause p xenv loc hyps tenv clauses
     
     print_string ("Match: " ^ (print_type xenv ty1) ^ "\n");*)
     ty

  | TeLoc (location, t) ->
     infer p xenv location hyps tenv t

(*and infer_clause
    (p : program)      
    (xenv : Export.env)
    (hyps : equations) 
    (tenv : tenv)      
    (clause : clause list)
    : ftype =
        
  match clause with
  | matching -> *)


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
      if equal inferred expected then
        ()
      else
        failwith "CHECK IS NOT COMPLETE YET!" (* do something here! *)

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
