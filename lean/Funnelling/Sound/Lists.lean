import Funnelling.Reduction

namespace Funnelling.SoundSimp

@[scoped simp] theorem listMem_iff {A : Type} {x : A} {l : List A} : List.Mem x l <-> Membership.mem l x := Iff.rfl

end Funnelling.SoundSimp

open Funnelling.SoundSimp

namespace Funnelling

theorem GTy.tys_eq_map : forall Gs : List GTy, GTy.tys Gs = Gs.map GTy.ty
  | [] => rfl
  | G :: Gs => by simp [GTy.tys, GTy.tys_eq_map Gs]

theorem Value.exprs_eq_map : forall vs : List Value, Value.exprs vs = vs.map Value.expr
  | [] => rfl
  | v :: vs => by simp [Value.exprs, Value.exprs_eq_map vs]

theorem Value.mem_exprs {v : Value} {vs : List Value} (h : List.Mem v vs) : List.Mem v.expr (Value.exprs vs) := by
  rw [Value.exprs_eq_map]; exact List.mem_map_of_mem h

theorem Ty.ftvList_eq_flatMap (Ts : List Ty) : Ty.ftvList Ts = Ts.flatMap Ty.ftv := by
  induction Ts <;> simp_all [Ty.ftvList]

theorem Expr.localsList_eq_flatMap (es : List Expr) : Expr.localsList es = es.flatMap Expr.locals := by
  induction es <;> simp_all [Expr.localsList]

theorem Method.localsList_eq_flatMap (Ms : List Method) : Method.localsList Ms = Ms.flatMap Method.locals := by
  induction Ms <;> simp_all [Method.localsList]

theorem Expr.ifVarsList_eq_flatMap (es : List Expr) : Expr.ifVarsList es = es.flatMap Expr.ifVars := by
  induction es <;> simp_all [Expr.ifVarsList]

theorem Method.ifVarsList_eq_flatMap (Ms : List Method) : Method.ifVarsList Ms = Ms.flatMap Method.ifVars := by
  induction Ms <;> simp_all [Method.ifVarsList]

theorem Expr.vbindersList_eq_flatMap (es : List Expr) : Expr.vbindersList es = es.flatMap Expr.vbinders := by
  induction es <;> simp_all [Expr.vbindersList]

theorem Method.vbindersList_eq_flatMap (Ms : List Method) : Method.vbindersList Ms = Ms.flatMap Method.vbinders := by
  induction Ms <;> simp_all [Method.vbindersList]

theorem Expr.tbindersList_eq_flatMap (es : List Expr) : Expr.tbindersList es = es.flatMap Expr.tbinders := by
  induction es <;> simp_all [Expr.tbindersList]

theorem Method.tbindersList_eq_flatMap (Ms : List Method) : Method.tbindersList Ms = Ms.flatMap Method.tbinders := by
  induction Ms <;> simp_all [Method.tbindersList]

theorem Expr.noShadowList_eq_all (Xs : List TVarName) (xs : List VarName) (es : List Expr) :
    Expr.noShadowList Xs xs es = es.all (Expr.noShadow Xs xs) := by
  induction es <;> simp_all [Expr.noShadowList]

theorem Method.noShadowList_eq_all (Xs : List TVarName) (xs : List VarName) (Ms : List Method) :
    Method.noShadowList Xs xs Ms = Ms.all (Method.noShadow Xs xs) := by
  induction Ms <;> simp_all [Method.noShadowList]

theorem Expr.closedList_eq_all (Xs : List TVarName) (xs : List VarName) (es : List Expr) :
    Expr.closedList Xs xs es = es.all (Expr.closed Xs xs) := by
  induction es <;> simp_all [Expr.closedList]

theorem Method.closedList_eq_all (Xs : List TVarName) (xs : List VarName) (Ms : List Method) :
    Method.closedList Xs xs Ms = Ms.all (Method.closed Xs xs) := by
  induction Ms <;> simp_all [Method.closedList]

theorem Expr.gsubstList_eq_map (s : GSubst) (es : List Expr) : Expr.gsubstList s es = es.map (Expr.gsubst s) := by
  induction es <;> simp_all [Expr.gsubstList]

theorem Method.gsubstList_eq_map (s : GSubst) (Ms : List Method) : Method.gsubstList s Ms = Ms.map (Method.gsubst s) := by
  induction Ms <;> simp_all [Method.gsubstList]

theorem Expr.vsubstList_eq_map (n : VSubst) (es : List Expr) : Expr.vsubstList n es = es.map (Expr.vsubst n) := by
  induction es <;> simp_all [Expr.vsubstList]

theorem Method.vsubstList_eq_map (n : VSubst) (Ms : List Method) : Method.vsubstList n Ms = Ms.map (Method.vsubst n) := by
  induction Ms <;> simp_all [Method.vsubstList]

theorem Ty.mem_ftvList {X : TVarName} {Ts : List Ty} :
    List.Mem X (Ty.ftvList Ts) <-> exists T, List.Mem T Ts /\ List.Mem X T.ftv := by
  rw [Ty.ftvList_eq_flatMap]; exact List.mem_flatMap

theorem Expr.mem_localsList {e : Expr} {es : List Expr} {k : K} (h : List.Mem e es) (hk : List.Mem k e.locals) :
    List.Mem k (Expr.localsList es) := by
  rw [Expr.localsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨e, h, hk⟩

theorem Method.mem_localsList {M : Method} {Ms : List Method} {k : K} (h : List.Mem M Ms) (hk : List.Mem k M.locals) :
    List.Mem k (Method.localsList Ms) := by
  rw [Method.localsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨M, h, hk⟩

theorem Expr.mem_ifVarsList {e : Expr} {es : List Expr} {x : VarName} (h : List.Mem e es) (hx : List.Mem x e.ifVars) :
    List.Mem x (Expr.ifVarsList es) := by
  rw [Expr.ifVarsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨e, h, hx⟩

theorem Method.mem_ifVarsList {M : Method} {Ms : List Method} {x : VarName} (h : List.Mem M Ms)
    (hx : List.Mem x M.ifVars) : List.Mem x (Method.ifVarsList Ms) := by
  rw [Method.ifVarsList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨M, h, hx⟩

theorem Expr.mem_vbindersList {e : Expr} {es : List Expr} {x : VarName} (h : List.Mem e es)
    (hx : List.Mem x e.vbinders) : List.Mem x (Expr.vbindersList es) := by
  rw [Expr.vbindersList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨e, h, hx⟩

theorem Method.mem_vbindersList {M : Method} {Ms : List Method} {x : VarName} (h : List.Mem M Ms)
    (hx : List.Mem x M.vbinders) : List.Mem x (Method.vbindersList Ms) := by
  rw [Method.vbindersList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨M, h, hx⟩

theorem Expr.mem_tbindersList {e : Expr} {es : List Expr} {X : TVarName} (h : List.Mem e es)
    (hX : List.Mem X e.tbinders) : List.Mem X (Expr.tbindersList es) := by
  rw [Expr.tbindersList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨e, h, hX⟩

theorem Method.mem_tbindersList {M : Method} {Ms : List Method} {X : TVarName} (h : List.Mem M Ms)
    (hX : List.Mem X M.tbinders) : List.Mem X (Method.tbindersList Ms) := by
  rw [Method.tbindersList_eq_flatMap]; exact List.mem_flatMap.mpr ⟨M, h, hX⟩

theorem Expr.noShadowList_mem {e : Expr} {es : List Expr} {Xs : List TVarName} {xs : List VarName} (h : List.Mem e es)
    (hn : Expr.noShadowList Xs xs es = true) : e.noShadow Xs xs = true := by
  rw [Expr.noShadowList_eq_all, List.all_eq_true] at hn; exact hn e h

theorem Method.noShadowList_mem {M : Method} {Ms : List Method} {Xs : List TVarName} {xs : List VarName}
    (h : List.Mem M Ms) (hn : Method.noShadowList Xs xs Ms = true) : M.noShadow Xs xs = true := by
  rw [Method.noShadowList_eq_all, List.all_eq_true] at hn; exact hn M h

theorem Expr.closedList_mem {e : Expr} {es : List Expr} {Xs : List TVarName} {xs : List VarName} (h : List.Mem e es)
    (hc : Expr.closedList Xs xs es = true) : e.closed Xs xs = true := by
  rw [Expr.closedList_eq_all, List.all_eq_true] at hc; exact hc e h

theorem Method.closedList_mem {M : Method} {Ms : List Method} {Xs : List TVarName} {xs : List VarName}
    (h : List.Mem M Ms) (hc : Method.closedList Xs xs Ms = true) : M.closed Xs xs = true := by
  rw [Method.closedList_eq_all, List.all_eq_true] at hc; exact hc M h

theorem Method.gsubstList_mem {s : GSubst} {M' : Method} {Ms : List Method} (h : List.Mem M' (Method.gsubstList s Ms)) :
    exists M, List.Mem M Ms /\ M' = M.gsubst s := by
  rw [Method.gsubstList_eq_map] at h; rcases List.mem_map.mp h with ⟨M, hM, e⟩; exact ⟨M, hM, e.symm⟩

theorem Method.vsubstList_mem {n : VSubst} {M' : Method} {Ms : List Method} (h : List.Mem M' (Method.vsubstList n Ms)) :
    exists M, List.Mem M Ms /\ M' = M.vsubst n := by
  rw [Method.vsubstList_eq_map] at h; rcases List.mem_map.mp h with ⟨M, hM, e⟩; exact ⟨M, hM, e.symm⟩

theorem ftvList_append {Ts Us : List Ty} : Ty.ftvList (Ts ++ Us) = Ty.ftvList Ts ++ Ty.ftvList Us := by
  simp [Ty.ftvList_eq_flatMap]

theorem vbindersList_append {es1 es2 : List Expr} :
    Expr.vbindersList (es1 ++ es2) = Expr.vbindersList es1 ++ Expr.vbindersList es2 := by
  simp [Expr.vbindersList_eq_flatMap]

theorem tbindersList_append {es1 es2 : List Expr} :
    Expr.tbindersList (es1 ++ es2) = Expr.tbindersList es1 ++ Expr.tbindersList es2 := by
  simp [Expr.tbindersList_eq_flatMap]

theorem noShadowList_append {Xs : List TVarName} {xs : List VarName} {es1 es2 : List Expr} :
    Expr.noShadowList Xs xs (es1 ++ es2) = (Expr.noShadowList Xs xs es1 && Expr.noShadowList Xs xs es2) := by
  simp [Expr.noShadowList_eq_all]

theorem Expr.gsubstList_append {s : GSubst} {es1 es2 : List Expr} :
    Expr.gsubstList s (es1 ++ es2) = Expr.gsubstList s es1 ++ Expr.gsubstList s es2 := by
  simp [Expr.gsubstList_eq_map]

theorem Expr.vsubstList_append {n : VSubst} {es1 es2 : List Expr} :
    Expr.vsubstList n (es1 ++ es2) = Expr.vsubstList n es1 ++ Expr.vsubstList n es2 := by
  simp [Expr.vsubstList_eq_map]

mutual
theorem GTy.ty_inj : forall {G G' : GTy}, G.ty = G'.ty -> G = G'
  | .cls C Gs, .cls C' Gs', h => by
    simp only [GTy.ty, Ty.cls.injEq] at h
    rw [h.1, GTy.tys_inj h.2]
theorem GTy.tys_inj : forall {Gs Gs' : List GTy}, GTy.tys Gs = GTy.tys Gs' -> Gs = Gs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [GTy.tys] at h
  | _ :: _, [], h => by simp [GTy.tys] at h
  | G :: Gs, G' :: Gs', h => by
    simp only [GTy.tys, List.cons.injEq] at h
    rw [GTy.ty_inj h.1, GTy.tys_inj h.2]
end

mutual
theorem Value.expr_inj : forall {v v' : Value}, v.expr = v'.expr -> v = v'
  | .new C Gs vs, .new C' Gs' vs', h => by
    simp only [Value.expr, Expr.new.injEq] at h
    rw [h.1, GTy.tys_inj h.2.1, Value.exprs_inj h.2.2]
  | .new _ _ _, .newLocal _ _ _ _ _ _, h => by simp [Value.expr] at h
  | .newLocal _ _ _ _ _ _, .new _ _ _, h => by simp [Value.expr] at h
  | .newLocal C Gs C' Gs' vs Ms, .newLocal D Hs D' Hs' ws Ns, h => by
    simp only [Value.expr, Expr.newLocal.injEq] at h
    have h2' : Gs = Hs := by
      apply GTy.tys_inj
      rw [GTy.tys_eq_map, GTy.tys_eq_map]
      have := congrArg (List.map Funnel.abs) h.2.1
      simpa [List.map_map, Function.comp_def, Funnel.abs] using this
    rw [h.1, h2', h.2.2.1, GTy.tys_inj h.2.2.2.1, Value.exprs_inj h.2.2.2.2.1, h.2.2.2.2.2]
theorem Value.exprs_inj : forall {vs vs' : List Value}, Value.exprs vs = Value.exprs vs' -> vs = vs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Value.exprs] at h
  | _ :: _, [], h => by simp [Value.exprs] at h
  | v :: vs, v' :: vs', h => by
    simp only [Value.exprs, List.cons.injEq] at h
    rw [Value.expr_inj h.1, Value.exprs_inj h.2]
end

theorem Value.of_mem_exprs {vs : List Value} {e : Expr} (h : List.Mem e (Value.exprs vs)) :
    exists v : Value, List.Mem v vs /\ e = v.expr := by
  rw [Value.exprs_eq_map] at h
  have h' := List.mem_map.mp h
  rcases h' with ⟨v, hv⟩; exact Exists.intro v (And.intro hv.1 hv.2.symm)

theorem Value.exprs_append_cons {vs : List Value} {es1 es2 : List Expr} {e : Expr}
    (h : Value.exprs vs = es1 ++ e :: es2) : exists v : Value, e = v.expr := by
  have hm : List.Mem e (Value.exprs vs) := by rw [h]; exact List.mem_append_right _ (List.Mem.head _)
  rcases Value.of_mem_exprs hm with ⟨v, hv⟩; exact Exists.intro v hv.2


section
variable {A B : Type} [DecidableEq A]

theorem lookup_cons_eq {a : A} {b : B} {r : List (Prod A B)} : List.lookup a ((a, b) :: r) = some b := by
  simp [List.lookup]

theorem lookup_cons_ne {a x : A} {b : B} {r : List (Prod A B)} (h : Not (x = a)) :
    List.lookup x ((a, b) :: r) = List.lookup x r := by
  have hb : (x == a) = false := by simp [h]
  simp [List.lookup, hb]

theorem lookup_mem {x : A} {y : B} : forall {r : List (Prod A B)}, List.lookup x r = some y ->
    List.Mem (x, y) r
  | [], h => by simp [List.lookup] at h
  | (a, b) :: r, h => by
    by_cases hx : x = a
    . subst hx; rw [lookup_cons_eq] at h; cases h; exact List.Mem.head _
    . rw [lookup_cons_ne hx] at h; exact List.Mem.tail _ (lookup_mem h)

theorem lookup_none {x : A} : forall {r : List (Prod A B)}, (forall p, List.Mem p r -> Not (p.1 = x)) ->
    List.lookup x r = none
  | [], _ => rfl
  | (a, b) :: r, h => by
    have hx : Not (x = a) := fun e => h (a, b) (List.Mem.head _) e.symm
    rw [lookup_cons_ne hx]
    exact lookup_none (fun p hp => h p (List.Mem.tail _ hp))

theorem lookup_none_of_not_dom {x : A} {r : List (Prod A B)} (h : Not (List.Mem x (r.map Prod.fst))) :
    List.lookup x r = none :=
  lookup_none fun p hp e => h (by rw [<- e]; exact List.mem_map_of_mem hp)

theorem lookup_isSome {x : A} : forall {r : List (Prod A B)}, List.Mem x (r.map Prod.fst) ->
    exists y, List.lookup x r = some y
  | [], h => by cases h
  | (a, b) :: r, h => by
    by_cases hx : x = a
    . subst hx; exact Exists.intro b lookup_cons_eq
    . rw [lookup_cons_ne hx]
      cases h with
      | head => exact absurd rfl hx
      | tail _ h => exact lookup_isSome h

theorem lookup_none_not_dom {x : A} {r : List (Prod A B)} (h : List.lookup x r = none) :
    Not (List.Mem x (r.map Prod.fst)) := by
  intro hm
  rcases lookup_isSome hm with ⟨v, hv⟩; rw [hv] at h; cases h

theorem lookup_append_left {x : A} : forall {r1 r2 : List (Prod A B)}, List.Mem x (r1.map Prod.fst) ->
    List.lookup x (r1 ++ r2) = List.lookup x r1
  | [], _, h => by cases h
  | (a, b) :: r1, r2, h => by
    by_cases hx : x = a
    . subst hx; simp [List.lookup]
    . rw [List.cons_append, lookup_cons_ne hx, lookup_cons_ne hx]
      cases h with
      | head => exact absurd rfl hx
      | tail _ h => exact lookup_append_left h

omit [DecidableEq A] in theorem zip_map_fst : forall {xs : List A} {ys : List B}, xs.length = ys.length -> (xs.zip ys).map Prod.fst = xs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact zip_map_fst (by simpa using h)

end

section
variable {A : Type} [DecidableEq A]

def rn (r : List (Prod A A)) (x : A) : A := (List.lookup x r).getD x

theorem rn_cons_eq {a b : A} {r : List (Prod A A)} : rn ((a, b) :: r) a = b := by simp [rn]

theorem rn_cons_ne {a b x : A} {r : List (Prod A A)} (h : Not (x = a)) : rn ((a, b) :: r) x = rn r x := by
  simp [rn, lookup_cons_ne h]

theorem rn_nil {x : A} : rn ([] : List (Prod A A)) x = x := rfl

theorem rn_id : forall {r : List (Prod A A)}, (forall p, List.Mem p r -> p.1 = p.2) -> forall x, rn r x = x
  | [], _, _ => rfl
  | (a, b) :: r, h, x => by
    by_cases hx : x = a
    . subst hx; rw [rn_cons_eq]; exact (h (x, b) (List.Mem.head _)).symm
    . rw [rn_cons_ne hx]; exact rn_id (fun p hp => h p (List.Mem.tail _ hp)) x

theorem rn_zip_mem : forall {xs ys : List A} {r : List (Prod A A)} {x : A}, xs.length = ys.length ->
    List.Mem x xs -> List.Mem (rn (xs.zip ys ++ r) x) ys
  | [], [], _, _, _, h => by cases h
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | a :: xs, b :: ys, r, x, hl, hx => by
    simp only [List.zip_cons_cons, List.cons_append]
    by_cases h : x = a
    . subst h; rw [rn_cons_eq]; exact List.Mem.head _
    . rw [rn_cons_ne h]
      cases hx with
      | head => exact absurd rfl h
      | tail _ hx => exact List.Mem.tail _ (rn_zip_mem (by simpa using hl) hx)

theorem rn_zip_not_mem : forall {xs ys : List A} {r : List (Prod A A)} {x : A},
    Not (List.Mem x xs) -> rn (xs.zip ys ++ r) x = rn r x
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | a :: xs, b :: ys, r, x, hx => by
    simp only [List.zip_cons_cons, List.cons_append]
    have h : Not (x = a) := fun e => hx (by rw [e]; exact List.Mem.head _)
    rw [rn_cons_ne h]
    exact rn_zip_not_mem (fun h' => hx (List.Mem.tail _ h'))

theorem rn_zip_comp : forall {xs ys zs : List A} {r1 r2 r3 : List (Prod A A)} {x : A},
    xs.length = ys.length -> ys.length = zs.length -> ys.Nodup -> List.Mem x xs ->
    rn (ys.zip zs ++ r2) (rn (xs.zip ys ++ r1) x) = rn (xs.zip zs ++ r3) x
  | [], _, _, _, _, _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h, _, _ => by simp at h
  | a :: xs, b :: ys, c :: zs, r1, r2, r3, x, h1, h2, hn, hx => by
    simp only [List.zip_cons_cons, List.cons_append]
    by_cases h : x = a
    . subst h; rw [rn_cons_eq, rn_cons_eq, rn_cons_eq]
    . rw [rn_cons_ne h, rn_cons_ne h]
      have hx' : List.Mem x xs := by
        cases hx with
        | head => exact absurd rfl h
        | tail _ hx => exact hx
      have hm := rn_zip_mem (r := r1) (by simpa using h1) hx'
      have hb : Not (rn (xs.zip ys ++ r1) x = b) := by intro e; rw [e] at hm; exact (List.nodup_cons.mp hn).1 hm
      rw [rn_cons_ne hb]
      exact rn_zip_comp (by simpa using h1) (by simpa using h2) (List.nodup_cons.mp hn).2 hx'

end

theorem VarName.ren_eq (rv : VRen) (x : VarName) : x.ren rv = rn rv x := rfl

theorem TVarName.ren_eq (rt : TRen) (X : TVarName) : X.ren rt = rn rt X := rfl

end Funnelling
