open Terms
open Atom
open Types
open Symbols

let get_Some : 'a option -> 'a = function
  | Some a -> a
  | _ -> failwith "Shouldn't be empty"

let ftv_env acc tenv = AtomMap.fold (fun key x y -> AtomSet.union (ftv x) y) tenv acc

let create_defunct_term (term : fterm) (arrow : Atom.atom) (apply : Atom.atom) t : fterm =
  let alpha1 = Atom.fresh (Identifier.mk "type" Syntax.type_sort) in
  let alpha2 = Atom.fresh (Identifier.mk "type" Syntax.type_sort) in
  let f = Atom.fresh (Identifier.mk "term" Syntax.term_sort) in
  let type_apply = foralls [alpha1; alpha2] (arrows [TyCon (arrow, [TyFreeVar alpha1; TyFreeVar alpha2]); TyFreeVar alpha1] (TyFreeVar alpha2)) in
  (*TeFix apply type_apply
        (TeTyAbs alpha1 (TeTyAbs alpha2
                                 (TeAbs (f, TyCon (arrow, [TyFreeVar alpha1; TyFreeVar alpha2]), , ref None) )))*) t
(*Eventually I'll need to add a list of clauses... I need to get this info in translate_term*)
        
let rec translate_type (arrow : Atom.atom) : ftype -> ftype = function
  | TyArrow (domain, codomain) ->
     TyCon (arrow, ([translate_type arrow domain; translate_type arrow codomain]))
      (* T -> T *)
  | TyForall context-> TyForall context

  | TyCon (k, body_type) -> TyCon (k, List.map (translate_type arrow) body_type) 
  (* tc T ... T *)
  | TyTuple (types) -> TyTuple (List.map (translate_type arrow) types)
  (* { T; ... T } *)
  | TyWhere (ty1, ty2, ty3) ->
     TyWhere ((translate_type arrow ty1), (translate_type arrow ty2), (translate_type arrow ty3))
  | ty -> ty
            
let rec translate_term (apply : Atom.atom) (arrow : Atom.atom) (prog : Terms.program) (d': datacon_table) : fterm -> fterm * datacon_table =
  function
  | TeVar at -> (TeVar at, d')
  (* x *)
  | TeAbs (at, domain, body, info) ->
     let info' = get_Some (!info) in
     let body_trans = translate_term apply arrow prog d' body in
     let m = Atom.fresh (Identifier.mk "lambda" Syntax.term_sort) in
     let free_var_eqs = List.fold_left AtomSet.union AtomSet.empty (List.map (fun (x1, x2) -> AtomSet.union (ftv x1) (ftv x2)) info'.hyps) in
     let fv = (ftv_env (ftv (info'.fty)) info'.tenv) in
     let free_var = AtomSet.union fv free_var_eqs in
     let types_list = List.map (fun x -> TyFreeVar x) (AtomSet.elements free_var) in
     let (dom_env, types) = List.split (AtomMap.bindings (info'.tenv)) in
     let env_var = List.map (fun x -> TeVar x) (dom_env) in
     (TeData (m, types_list, env_var), d')
       
  | TeApp (t1, t2, info) ->
     let info' = get_Some (!info) in
     let (term1, d1') = translate_term apply arrow prog d' t1 in
     let (term2, d2') = translate_term apply arrow prog d' t2 in
     (TeData (apply, [translate_type arrow info'.domain; translate_type arrow info'.codomain], [term1; term2]), d')
       
  | TeLet (at, t1, t2) ->
     let (t1_trans, d1') = translate_term apply arrow prog d' t1 in 
     let (t2_trans, d2') = translate_term apply arrow prog d' t2 in 

     (TeLet (at, t1_trans, t2_trans), d2')
  (* let x = t in t *)
  | TeFix (at, ty, t) ->
     let (t_trans, d1') = translate_term apply arrow prog d' t in
     let ty_trans = translate_type arrow ty in
     (TeFix (at, ty_trans, t_trans), d1')
       
  | TeTyAbs (at, term) ->
     let (term_trans, d1') = translate_term apply arrow prog d' term in
     (TeTyAbs (at, term_trans), d1')
       
  | TeTyApp (term, ty) ->
     let (term_trans, d1') = translate_term apply arrow prog d' term in
     let ty_trans = translate_type arrow ty in
     (TeTyApp (term_trans, ty_trans), d1')
  (* t [ T ] *)
  | TeData (k, types, terms) ->
     let terms_trans = List.map (fun x -> fst (translate_term apply arrow prog d' x)) terms in
     let types_trans = List.map (translate_type arrow) types in
     (TeData (k, types_trans, terms_trans), d')

  | TeTyAnnot (term, ty) ->
     let (term_trans, d1') = translate_term apply arrow prog d' term in
     let ty_trans = translate_type arrow ty in
     (TeTyAnnot (term_trans, ty_trans), d1')
  (* (t : T) *)
  | TeMatch (term, ty, clauses) ->
     let (term_trans, d1') = translate_term apply arrow prog d' term in
     let ty_trans = translate_type arrow ty in
     (TeMatch (term_trans, ty_trans, clauses), d1')
  (* match t return T with clause ... clause end *)
  | TeLoc (location, term) ->
     let (term_trans, d1') = translate_term apply arrow prog d' term in
     (TeLoc (location, term_trans), d1')
       
  
let translate (prog : Terms.program) =
  prog
