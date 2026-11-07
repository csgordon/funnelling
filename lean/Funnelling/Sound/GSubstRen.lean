import Funnelling.Sound.SubstRen

namespace Funnelling.High

mutual
theorem GTy.ftv_ty : forall (G : GTy), G.ty.ftv = []
  | .cls C Gs => by simp only [GTy.ty, Ty.ftv]; exact GTy.ftv_tys Gs
theorem GTy.ftv_tys : forall (Gs : List GTy), Ty.ftvList (GTy.tys Gs) = []
  | [] => rfl
  | G :: Gs => by simp only [GTy.tys, Ty.ftvList, GTy.ftv_ty G, GTy.ftv_tys Gs]; rfl
end

theorem GTy.ren_ty {rt : TRen} (G : GTy) : G.ty.ren rt = G.ty :=
  Ty.ren_id (fun X hX => by rw [GTy.ftv_ty] at hX; cases hX)

theorem GSubst.lookup_ty {sigma : GSubst} {X : TVarName} :
    List.lookup X sigma.ty = (List.lookup X sigma).map GTy.ty := by
  induction sigma with
  | nil => rfl
  | cons p sigma ih =>
    cases p with
    | mk a G =>
      simp only [GSubst.ty, List.map_cons]
      by_cases e : X = a
      . subst e; rw [lookup_cons_eq, lookup_cons_eq]; rfl
      . rw [lookup_cons_ne e, lookup_cons_ne e]; exact ih

abbrev NotDomT (Xs : List TVarName) (sigma : GSubst) : Prop :=
  forall X, List.Mem X Xs -> Not (List.Mem X (sigma.map Prod.fst))

theorem lookupT_none_of_notDom {sigma : GSubst} {X : TVarName} (h : Not (List.Mem X (sigma.map Prod.fst))) :
    List.lookup X sigma = none := by
  apply lookup_none
  intro p hp e
  apply h
  rw [<- e]
  exact List.mem_map_of_mem hp

structure GSEnv (rt rto : TRen) (s1 s2 : GSubst) (T : List TVarName) : Prop where
  st : forall X, List.Mem X T ->
    (exists G, List.lookup X s1 = some G /\ List.lookup (rn rt X) s2 = some G) \/
    (List.lookup X s1 = none /\ List.lookup (rn rt X) s2 = none /\ rn rt X = rn rto X)

theorem GSEnv.var {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T)
    {X : TVarName} (hX : List.Mem X T) :
    ((Ty.var X).ren rt).subst s2.ty = ((Ty.var X).subst s1.ty).ren rto := by
  rcases env.st X hX with h | h
  . cases h with
    | intro G hG =>
      simp only [Ty.ren, Ty.subst, GSubst.lookup_ty, TVarName.ren_eq, hG.1, hG.2, Option.map_some,
        Option.getD_some, GTy.ren_ty]
  . simp only [Ty.ren, Ty.subst, GSubst.lookup_ty, TVarName.ren_eq, h.1, h.2.1, Option.map_none,
      Option.getD_none]
    rw [h.2.2]

mutual
theorem GSEnv.ty {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T) :
    forall {U : Ty}, (forall X, List.Mem X U.ftv -> List.Mem X T) -> (U.ren rt).subst s2.ty = (U.subst s1.ty).ren rto
  | .var X, h => env.var (h X (by simp [Ty.ftv]))
  | .cls C Us, h => by
    simp only [Ty.ren, Ty.subst]
    rw [GSEnv.tys env (fun X hX => h X (by simpa [Ty.ftv] using hX))]
theorem GSEnv.tys {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T) :
    forall {Us : List Ty}, (forall X, List.Mem X (Ty.ftvList Us) -> List.Mem X T) ->
      Ty.substList s2.ty (Ty.renList rt Us) = Ty.renList rto (Ty.substList s1.ty Us)
  | [], _ => rfl
  | U :: Us, h => by
    simp only [Ty.renList, Ty.substList]
    rw [GSEnv.ty env (fun X hX => h X (List.mem_append_left _ hX)),
      GSEnv.tys env (fun X hX => h X (List.mem_append_right _ hX))]
end

theorem GSEnv.funnels {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T) :
    forall {Fs : List Funnel}, (forall X, List.Mem X (domF Fs) -> List.Mem X T) ->
      (Fs.map (Funnel.ren rt)).map (Funnel.gsubst s2) = (Fs.map (Funnel.gsubst s1)).map (Funnel.ren rto)
  | [], _ => rfl
  | F :: Fs, h => by
    simp only [List.map_cons, List.cons.injEq]
    refine And.intro ?_ (GSEnv.funnels env (fun X hX => h X (by rw [domF_cons]; exact List.mem_append_right _ hX)))
    cases F with
    | ground G => rfl
    | funnel X =>
      have hX : List.Mem X T := h X (by simp [domF])
      rcases env.st X hX with h' | h'
      . cases h' with
        | intro G hG => simp only [Funnel.ren, Funnel.gsubst, TVarName.ren_eq, hG.1, hG.2]
      . simp only [Funnel.ren, Funnel.gsubst, TVarName.ren_eq, h'.1, h'.2.1]
        rw [h'.2.2]

theorem GSEnv.methExt {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T)
    {Xa Xb : List TVarName} (hl : Xa.length = Xb.length) (ha : NotDomT Xa s1) (hb : NotDomT Xb s2) :
    GSEnv (Xa.zip Xb ++ rt) (Xa.zip Xb ++ rto) s1 s2 (T ++ Xa) where
  st := by
    intro X hX
    by_cases hm : List.Mem X Xa
    . have hmb := rn_zip_mem (r := rt) hl hm
      exact Or.inr (And.intro (lookupT_none_of_notDom (ha X hm))
        (And.intro (lookupT_none_of_notDom (hb _ hmb)) (rn_zip_indep hl hm)))
    . rw [rn_zip_not_mem hm, rn_zip_not_mem hm]
      have hXT : List.Mem X T := by
        simp only [listMem_iff, List.mem_append] at hX hm
        rcases hX with h | h
        . exact h
        . exact absurd h hm
      exact env.st X hXT

theorem notDomT_append_left {xs ys : List TVarName} {s : GSubst} (h : NotDomT (xs ++ ys) s) : NotDomT xs s :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem notDomT_append_right {xs ys : List TVarName} {s : GSubst} (h : NotDomT (xs ++ ys) s) : NotDomT ys s :=
  fun x hx => h x (List.mem_append_right _ hx)

theorem bounds_subst_ren {r1 r2 : TRen} {s1 s2 : TSubst} : forall {Delta : Bounds} {Xs : List TVarName},
    Xs.length = Delta.length ->
    (forall b, List.Mem b Delta -> (b.T.ren r1).subst s2 = (b.T.subst s1).ren r2) ->
    Bounds.subst s2 ((Delta.zip Xs).map fun p => ({ X := p.2, T := p.1.T.ren r1 } : Bound)) =
      ((Bounds.subst s1 Delta).zip Xs).map fun p => ({ X := p.2, T := p.1.T.ren r2 } : Bound)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: Delta, X :: Xs, hl, h => by
    simp only [Bounds.subst, List.zip_cons_cons, List.map_cons, List.cons.injEq] at |-
    refine And.intro ?_ (bounds_subst_ren (by simpa using hl) (fun b' hb' => h b' (List.Mem.tail _ hb')))
    rw [h b (List.Mem.head _)]

theorem params_subst_ren {r1 r2 : TRen} {s1 s2 : TSubst} : forall {ps : List VarDecl} {xs : List VarName},
    xs.length = ps.length ->
    (forall p, List.Mem p ps -> (p.T.ren r1).subst s2 = (p.T.subst s1).ren r2) ->
    ((ps.zip xs).map fun p => ({ T := p.1.T.ren r1, x := p.2 } : VarDecl)).map (VarDecl.subst s2) =
      ((ps.map (VarDecl.subst s1)).zip xs).map fun p => ({ T := p.1.T.ren r2, x := p.2 } : VarDecl)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | p :: ps, x :: xs, hl, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, VarDecl.subst]
    refine And.intro ?_ (params_subst_ren (by simpa using hl) (fun p' hp' => h p' (List.Mem.tail _ hp')))
    rw [h p (List.Mem.head _)]

theorem dom_bounds_subst {s : TSubst} {Delta : Bounds} : dom (Bounds.subst s Delta) = dom Delta := by
  simp [dom, Bounds.subst, List.map_map, Function.comp_def]

mutual
theorem RenE.gsub {rv rt a b} : RenE rv rt a b -> forall {rto s1 s2 T S}, GSEnv rt rto s1 s2 T ->
    a.closed T S = true -> NotDomT a.tbinders s1 -> NotDomT b.tbinders s2 ->
    RenE rv rto (a.gsubst s1) (b.gsubst s2)
  | .var, _, _, _, _, _, _, _, _, _ => by simp only [Expr.gsubst]; exact RenE.var
  | .call h1 hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.tbinders] at hd1 hd2
    simp only [Expr.gsubst]
    rw [env.tys (all_contains_iff.mp hc.1.2)]
    exact RenE.call (RenE.gsub h1 env hc.1.1 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenEs.gsub hs1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
  | .superCall h1 hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.tbinders] at hd1 hd2
    simp only [Expr.gsubst]
    have h2 := all_contains_iff.mp hc.1.2
    rw [env.tys (fun X hX => h2 X (List.mem_append_right _ hX)),
      env.ty (fun X hX => h2 X (List.mem_append_left _ hX))]
    exact RenE.superCall (RenE.gsub h1 env hc.1.1 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenEs.gsub hs1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
  | .field h1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed] at hc
    simp only [Expr.tbinders] at hd1 hd2
    simp only [Expr.gsubst]
    exact RenE.field (RenE.gsub h1 env hc hd1 hd2)
  | .new hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.tbinders] at hd1 hd2
    simp only [Expr.gsubst]
    rw [env.tys (all_contains_iff.mp hc.1)]
    exact RenE.new (RenEs.gsub hs1 env hc.2 hd1 hd2)
  | .newLocal hs1 hm1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.tbinders] at hd1 hd2
    simp only [Expr.gsubst]
    have h1 := all_contains_iff.mp hc.1.1
    rw [env.tys (fun X hX => h1 X (List.mem_append_right _ hX)),
      env.funnels (fun X hX => h1 X (List.mem_append_left _ hX))]
    exact RenE.newLocal (RenEs.gsub hs1 env hc.1.2 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenMs.gsub hm1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
  | .ifInst h01 h11 h21, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.tbinders] at hd1 hd2
    simp only [Expr.gsubst]
    rw [env.ty (all_contains_iff.mp hc.1.1.2)]
    exact RenE.ifInst
      (RenE.gsub h01 env hc.1.1.1 (notDomT_append_left (notDomT_append_left hd1))
        (notDomT_append_left (notDomT_append_left hd2)))
      (RenE.gsub h11 env hc.1.2 (notDomT_append_right (notDomT_append_left hd1))
        (notDomT_append_right (notDomT_append_left hd2)))
      (RenE.gsub h21 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
theorem RenEs.gsub {rv rt as bs} : RenEs rv rt as bs -> forall {rto s1 s2 T S}, GSEnv rt rto s1 s2 T ->
    Expr.closedList T S as = true -> NotDomT (Expr.tbindersList as) s1 -> NotDomT (Expr.tbindersList bs) s2 ->
    RenEs rv rto (Expr.gsubstList s1 as) (Expr.gsubstList s2 bs)
  | .nil, _, _, _, _, _, _, _, _, _ => RenEs.nil
  | .cons h1 hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closedList, Bool.and_eq_true] at hc
    simp only [Expr.tbindersList] at hd1 hd2
    simp only [Expr.gsubstList]
    exact RenEs.cons (RenE.gsub h1 env hc.1 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenEs.gsub hs1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
theorem RenM.gsub {rv rt Ma Mb} : RenM rv rt Ma Mb -> forall {rto s1 s2 T S}, GSEnv rt rto s1 s2 T ->
    Ma.closed T S = true -> NotDomT Ma.tbinders s1 -> NotDomT Mb.tbinders s2 ->
    RenM rv rto (Ma.gsubst s1) (Mb.gsubst s2)
  | .mk (Delta := Da) (T0 := T0) (m := m) (ps := ps) (Xs' := Xs) (xs' := xs) hL hl h1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Method.closed, Bool.and_eq_true] at hc
    simp only [Method.tbinders] at hd1 hd2
    rw [dom_renBounds hL] at hd2
    simp only [Method.gsubst]
    have hLa : (dom Da).length = Xs.length := by simp [dom, hL]
    have env' := env.methExt hLa (notDomT_append_left hd1) (notDomT_append_left hd2)
    have hbody := RenE.gsub h1 env' hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2)
    have hm := RenM.mk (rv := rv) (rt := rto) (Delta := Bounds.subst s1.ty Da) (T0 := T0.subst s1.ty) (m := m)
      (ps := ps.map (VarDecl.subst s1.ty)) (Xs' := Xs) (xs' := xs) (by simp [Bounds.subst, hL]) (by simp [hl])
      (by rw [dom_bounds_subst]; simpa [List.map_map, Function.comp_def, VarDecl.subst] using hbody)
    have hall := all_contains_iff.mp hc.1
    rw [dom_bounds_subst] at hm
    rw [env'.ty (fun X hX => hall X (by simp only [List.cons_append]; exact List.mem_append_left _ hX)),
      bounds_subst_ren hL (fun b hb => env'.ty (fun X hX => hall X (by
        simp only [List.cons_append, Ty.ftvList, List.append_eq]
        exact List.mem_append_right _ (by rw [ftvList_append]; exact List.mem_append_left _ (ftvList_map_mem (f := Bound.T) hb hX))))),
      params_subst_ren hl (fun p hp => env'.ty (fun X hX => hall X (by
        simp only [List.cons_append, Ty.ftvList, List.append_eq]
        exact List.mem_append_right _ (by rw [ftvList_append]; exact List.mem_append_right _ (ftvList_map_mem (f := VarDecl.T) hp hX)))))]
    exact hm
theorem RenMs.gsub {rv rt Mas Mbs} : RenMs rv rt Mas Mbs -> forall {rto s1 s2 T S}, GSEnv rt rto s1 s2 T ->
    Method.closedList T S Mas = true -> NotDomT (Method.tbindersList Mas) s1 ->
    NotDomT (Method.tbindersList Mbs) s2 ->
    RenMs rv rto (Method.gsubstList s1 Mas) (Method.gsubstList s2 Mbs)
  | .nil, _, _, _, _, _, _, _, _, _ => RenMs.nil
  | .cons h1 hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Method.closedList, Bool.and_eq_true] at hc
    simp only [Method.tbindersList] at hd1 hd2
    simp only [Method.gsubstList]
    exact RenMs.cons (RenM.gsub h1 env hc.1 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenMs.gsub hs1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
end

end Funnelling.High