open Terms
open Atom
open Types
open Symbols

let deconstruct_arrow = function
  | TyArrow (t1, t2) -> (t1, t2)
  | _ -> failwith "Not an arrow type"
       
let get_Some : 'a option -> 'a = function
  | Some a -> a
  | _ -> failwith "Shouldn't be empty"

(*Gets every free variable in the environment*)
let ftv_env acc tenv = AtomMap.fold (fun key x y -> AtomSet.union (ftv x) y) tenv acc

(*Will be used when building the defunctionalization*)
let clauses : clause list ref = ref []
                                    
(*Creates the packaging around the new term (as described in the paper)*)
let create_defunct_term (arrow : Atom.atom) (apply : Atom.atom) : fterm =
  let alpha1 = Atom.fresh (Identifier.mk "alpha1" Syntax.type_sort) in
  let alpha2 = Atom.fresh (Identifier.mk "alpha2" Syntax.type_sort) in
  let f = Atom.fresh (Identifier.mk "f" Syntax.term_sort) in
  let arg = Atom.fresh (Identifier.mk "arg" Syntax.term_sort) in
  (*\tau_apply*)
  let type_apply = foralls [alpha1; alpha2] (arrows [TyCon (arrow, [TyFreeVar alpha1; TyFreeVar alpha2]); TyFreeVar alpha1] (TyFreeVar alpha2)) in
  clauses := List.map (fun cl ->
                 match cl with
                 | Clause (pat, TeLet (at, TeTyAnnot (t1, ty), t2)) -> Clause (pat, TeLet (at, TeTyAnnot (TeVar arg, ty), t2))
                 | _ -> assert false)
                      !clauses;
  let t = TeMatch (TeVar f, TyFreeVar alpha2, !clauses) in
  let t = TeAbs (arg, TyFreeVar alpha1, t, ref None) in
  let t = TeAbs (f, TyCon (arrow, [TyFreeVar alpha1; TyFreeVar alpha2]), t, ref None) in
  let t = TeTyAbs (alpha1, (TeTyAbs (alpha2, t))) in
  TeFix (apply, type_apply, t)

let rec translate_type (arrow : Atom.atom) : ftype -> ftype = function
  (* T -> T *)
  | TyArrow (TyTuple t1, TyCon (t2, tl2)) ->
     TyArrow (translate_type arrow (TyTuple t1), translate_type arrow (TyCon (t2, tl2)))
  | TyArrow (domain, codomain) ->
     TyCon (arrow, ([translate_type arrow domain; translate_type arrow codomain]))
  (*\forall ctx*)
  | TyForall context->
     let at = Atom.fresh (hint context) in
     TyForall (abstract at (translate_type arrow (fill context (TyFreeVar at)) ))
  (* tc T ... T *)
  | TyCon (k, body_type) -> TyCon (k, List.map (translate_type arrow) body_type) 
  (* { T; ... T } *)
  | TyTuple (types) -> TyTuple (List.map (translate_type arrow) types)
  (*ty1 where (ty2 = ty3)*)
  | TyWhere (ty1, ty2, ty3) ->
     TyWhere ((translate_type arrow ty1), (translate_type arrow ty2), (translate_type arrow ty3))
  (*If it's a variable, it stays the same*)
  | ty -> ty
            
let rec translate_term (apply : Atom.atom) (arrow : Atom.atom) (d': datacon_table ref) : fterm -> fterm =
  function
  | TeVar at -> TeVar at
  (* x *)
  | TeAbs (at, domain, body, info) ->
     let info' = get_Some (!info) in
     let body_trans = translate_term apply arrow d' body in
     (*Fresh label*)
     let m = Atom.fresh (Identifier.mk "M" Syntax.term_sort) in
     (*Begin to gather all the free variables in C, Gamma, tau1, tau2*)
     (*C*)
                  
     let free_var_eqs = List.fold_left AtomSet.union AtomSet.empty (List.map (fun (x1, x2) -> AtomSet.union (ftv x1) (ftv x2)) info'.hyps) in
     let (dom, codom) = deconstruct_arrow info'.fty in
     let fv = (ftv_env (AtomSet.union (ftv dom) (ftv codom)) info'.tenv) in
     (*All the type free variables we need for the rule described in the paper*)
     let free_var = AtomSet.union fv free_var_eqs in
     (*Convert the types to a list*)
     let types_list = List.map (fun x -> TyFreeVar x) (AtomSet.elements free_var) in
     (*Get every variable in the environment*)
     let (dom_env, types) = List.split (AtomMap.bindings (info'.tenv)) in
     let env_var = List.map (fun x -> TeVar x) (dom_env) in
     (*Add a new constructor to the signature*)
     let abs_type = (foralls (AtomSet.elements free_var) (wheres (TyArrow ((TyTuple (List.map (translate_type arrow) types)), (TyCon (arrow, ([translate_type arrow dom; translate_type arrow codom]))))) info'.hyps)) in
     let abs_type = translate_type arrow abs_type in
     d' := AtomMap.add m abs_type !d';
     (*add a new clause to the defunctionalized term*)
     clauses := (Clause (PatData (Error.dummy, m, AtomSet.elements free_var, dom_env), TeLet (at, TeTyAnnot (body_trans, translate_type arrow domain), body_trans))) :: !clauses;
     TeData (m, types_list, env_var)
            
  | TeApp (t1, t2, info) ->
     let info' = get_Some (!info) in
     let term1 = translate_term apply arrow d' t1 in
     let term2 = translate_term apply arrow d' t2 in
     TeApp ( TeApp ( TeTyApp ( TeTyApp ( (TeVar apply), translate_type arrow (info'.domain)) ,
                                translate_type arrow (info'.codomain)),
                      term1, info), 
              term2, info)
       
  | TeLet (at, t1, t2) ->
     let t1_trans = translate_term apply arrow d' t1 in 
     let t2_trans = translate_term apply arrow d' t2 in 

     TeLet (at, t1_trans, t2_trans)
  (* let x = t in t *)
  | TeFix (at, ty, t) ->
     let t_trans = translate_term apply arrow d' t in
     let ty_trans = translate_type arrow ty in
     TeFix (at, ty_trans, t_trans)
       
  | TeTyAbs (at, term) ->
     let term_trans = translate_term apply arrow d' term in
     TeTyAbs (at, term_trans)
       
  | TeTyApp (term, ty) ->
     let term_trans = translate_term apply arrow d' term in
     let ty_trans = translate_type arrow ty in
     TeTyApp (term_trans, ty_trans)
  (* t [ T ] *)
  | TeData (k, types, terms) ->
     let terms_trans = List.map (translate_term apply arrow d') terms in
     let types_trans = List.map (translate_type arrow) types in
     TeData (k, types_trans, terms_trans)

  | TeTyAnnot (term, ty) ->
     let term_trans = translate_term apply arrow d' term in
     let ty_trans = translate_type arrow ty in
     TeTyAnnot (term_trans, ty_trans)
  (* (t : T) *)
  | TeMatch (term, ty, clauses) ->
     let term_trans = translate_term apply arrow d' term in
     let ty_trans = translate_type arrow ty in
     let clauses' = List.map (fun (Clause (p, t)) -> Clause (p, translate_term apply arrow d' t)) clauses in
     TeMatch (term_trans, ty_trans, clauses')
  (* match t return T with clause ... clause end *)

  | TeLoc (location, term) ->
     let term_trans = translate_term apply arrow d' term in
     TeLoc (location, term_trans)
  
let translate (prog : Terms.program) =
  let Prog (type_table, data_con, t) = prog in
  let apply = Atom.fresh (Identifier.mk "apply" Syntax.term_sort) in
  let arrow = Atom.fresh (Identifier.mk "arrow" Syntax.type_sort) in
  let type_table = AtomMap.add arrow 2 type_table in
  (* We translate all data constructors to replace lambda abstractions by Arrow *)
  let data_con = AtomMap.map (translate_type arrow) data_con in
  let d' = ref data_con in
  let t' = translate_term apply arrow d' t in
  let t' = TeLet (apply, create_defunct_term arrow apply, t') in
  Prog (type_table, !d', t')
