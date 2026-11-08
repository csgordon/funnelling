import Funnelling.Sound.GSubT
import Funnelling.Sound.IfThen

open Funnelling.SoundSimp

namespace Funnelling.High

theorem lookup_zip_vars {X : TVarName} : forall {Xs : List TVarName}, List.Mem X Xs ->
    List.lookup X (Xs.zip (vars Xs)) = some (Ty.var X)
  | [], h => by cases h
  | Y :: Xs, h => by
    simp only [vars, List.map_cons, List.zip_cons_cons]
    by_cases e : X = Y
    . subst e; exact lookup_cons_eq
    . rw [lookup_cons_ne e]
      cases h with
      | head => exact absurd rfl e
      | tail _ h => exact lookup_zip_vars h

theorem substList_bind_vars_id {Dl : Bounds} {L : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom Dl)) :
    Ty.substList (bind Dl (vars (dom Dl))) L = L := by
  apply Ty.substList_id
  intro X hX
  simp only [Ty.subst, bind, lookup_zip_vars (h X hX), Option.getD_some]

theorem vars_append {Xs Ys : List TVarName} : vars (Xs ++ Ys) = vars Xs ++ vars Ys := by simp [vars]

theorem ftv_vars {X : TVarName} {Xs : List TVarName} (h : List.Mem X (Ty.ftvList (vars Xs))) : List.Mem X Xs := by
  rcases ftvList_mem.mp h with ⟨T, hT⟩
  simp only [vars, listMem_iff, List.mem_map] at hT
  rcases hT.1 with ⟨Y, hY⟩; rw [<- hY.2] at hT; have := hT.2; simp [Ty.ftv] at this; rw [this]; exact hY.1

theorem dec_override {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {D : Dec}
    (hD : Declared d (.dec D)) {M : Method} (hM : List.Mem M D.Ms) {D0 : Dec} (hD0 : Declared d (.dec D0))
    {Gs Ts0 : List Ty} (hl : Gs.length = D.bounds.length) (hs : Sub d [] (.cls D.C Gs) (.cls D0.C Ts0)) :
    exists Us, Ts0 = Ty.substList (bind D.bounds Gs) Us /\ OverrideOkM d (.cls D0.C Us) M /\
      forall X, List.Mem X (Ty.ftvList Us) -> List.Mem X (dom D.bounds) := by
  have hn := (sf_dec hwf hok hD).ndom
  have e : Gs = Ty.substList (bind D.bounds Gs) (vars (dom D.bounds)) :=
    (vars_subst hn (by rw [hl]; simp [dom])).symm
  rw [e] at hs
  rcases Sub.inv_subst hd (Delta2 := D.bounds) (A := dom D.bounds) hs rfl (fun X hX => ftv_vars hX) with ⟨T0, h0⟩
  rcases Sub.cls_target h0.2.1 rfl with ⟨C1, U0, e0⟩
  subst e0
  have e1 := h0.1
  simp only [Ty.subst, Ty.cls.injEq] at e1
  have e2 := e1.1
  subst e2
  refine Exists.intro U0 (And.intro e1.2 (And.intro ?_ h0.2.2))
  rcases Sub.dec_step hwf hD h0.2.1 with e3 | e3
  . simp only [Ty.cls.injEq] at e3
    have eD := Declared.unique hwf hD hD0 e3.1.symm
    cases eD
    rw [e3.2]
    cases M with
    | mk Dm T0m m ps e =>
      have hcl := declMeth_closed hwf hok hD hM
      simp only [K.gvars, <- dom_append] at hcl
      have hv : vars (dom D.bounds) ++ vars (dom Dm) = vars (dom (D.bounds ++ Dm)) := by rw [dom_append, vars_append]
      refine OverrideOkM.dec hD hM (by simp [vars, dom]) rfl ?_ ?_
      . rw [hv, substList_bind_vars_id hcl.1]
      . rw [hv, substList_bind_vars_id hcl.2]
  . have hsup : (Ty.cls D.C' D.Ts).subst (bind D.bounds (vars (dom D.bounds))) = Ty.cls D.C' D.Ts := by
      simp only [Ty.subst]
      rw [substList_bind_vars_id (hd.supD D hD)]
    rw [hsup] at e3
    exact (hok D hD.dec_mem).2.2.2 M D0.C U0 hM e3.2


mutual
theorem Expr.noShadow_tscope : forall {e : Expr} {Xs Xs2 : List TVarName} {xs : List VarName},
    e.noShadow Xs xs = true -> (forall X, List.Mem X e.tbinders -> List.Mem X Xs2 -> List.Mem X Xs) ->
    e.noShadow Xs2 xs = true
  | .var _, _, _, _, _, _ => rfl
  | .call e _ _ es, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
  | .superCall e _ _ _ es, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
  | .field e _, _, _, _, h, hs => by
    simp only [Expr.noShadow] at h |-
    exact Expr.noShadow_tscope h hs
  | .new _ _ es, _, _, _, h, hs => Expr.noShadowList_tscope h hs
  | .newLocal _ _ _ _ es Ms, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadowList_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Method.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
  | .ifInst e0 _ _ e1 e2, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (And.intro (And.intro (Expr.noShadow_tscope h.1.1.1 (fun y hy => hs y (Or.inl (Or.inl hy))))
      h.1.1.2) (Expr.noShadow_tscope h.1.2 (fun y hy => hs y (Or.inl (Or.inr hy)))))
      (Expr.noShadow_tscope h.2 (fun y hy => hs y (Or.inr hy)))
theorem Expr.noShadowList_tscope : forall {es : List Expr} {Xs Xs2 : List TVarName} {xs : List VarName},
    Expr.noShadowList Xs xs es = true -> (forall X, List.Mem X (Expr.tbindersList es) -> List.Mem X Xs2 -> List.Mem X Xs) ->
    Expr.noShadowList Xs2 xs es = true
  | [], _, _, _, _, _ => rfl
  | e :: es, _, _, _, h, hs => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at h |-
    simp only [Expr.tbindersList, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
theorem Method.noShadow_tscope : forall {M : Method} {Xs Xs2 : List TVarName} {xs : List VarName},
    M.noShadow Xs xs = true -> (forall X, List.Mem X M.tbinders -> List.Mem X Xs2 -> List.Mem X Xs) ->
    M.noShadow Xs2 xs = true
  | .mk Dl _ _ ps e, Xs, Xs2, _, h, hs => by
    simp only [Method.noShadow, Bool.and_eq_true] at h |-
    simp only [Method.tbinders, listMem_iff, List.mem_append] at hs
    refine And.intro (And.intro (all_not_contains_of (fun X hX hm =>
      not_mem_of_all_not_contains h.1.1 hX (hs X (Or.inl hX) hm))) h.1.2) ?_
    refine Expr.noShadow_tscope h.2 (fun y hy hm => ?_)
    simp only [listMem_iff, List.mem_append] at hm |-
    rcases hm with hm | hm
    . exact Or.inl (hs y (Or.inr hy) hm)
    . exact Or.inr hm
theorem Method.noShadowList_tscope : forall {Ms : List Method} {Xs Xs2 : List TVarName} {xs : List VarName},
    Method.noShadowList Xs xs Ms = true ->
    (forall X, List.Mem X (Method.tbindersList Ms) -> List.Mem X Xs2 -> List.Mem X Xs) ->
    Method.noShadowList Xs2 xs Ms = true
  | [], _, _, _, _, _ => rfl
  | M :: Ms, _, _, _, h, hs => by
    simp only [Method.noShadowList, Bool.and_eq_true] at h |-
    simp only [Method.tbindersList, listMem_iff, List.mem_append] at hs
    exact And.intro (Method.noShadow_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Method.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
end

theorem typingSeq_lookup {d : Decls} : forall {g : Gamma} {vs : List Value},
    (gdom g).Nodup -> TypingSeq d [] [] (Value.exprs vs) (g.map VarDecl.T) ->
    forall x v U, List.lookup x ((gdom g).zip vs) = some v -> g.lookup x = some U -> Typing d [] [] v.expr U
  | [], _, _, _, x, v, U, _, h => by simp [Gamma.lookup] at h
  | _ :: _, [], _, h, _, _, _, _, _ => by cases h
  | y :: g, v0 :: vs, hn, h, x, v, U, h1, h2 => by
    cases h with
    | cons ht hts =>
      simp only [gdom, List.map_cons, List.zip_cons_cons] at h1 hn
      by_cases e : x = y.x
      . subst e
        rw [lookup_cons_eq] at h1
        cases h1
        simp only [Gamma.lookup, List.find?_cons, beq_self_eq_true, Option.map_some] at h2
        cases h2
        exact ht
      . rw [lookup_cons_ne e] at h1
        have hb : (y.x == x) = false := by simpa using fun h => e h.symm
        simp only [Gamma.lookup, List.find?_cons, hb] at h2
        exact typingSeq_lookup (List.nodup_cons.mp hn).2 hts x v U h1 h2

theorem gsubst_ty_bind {Dl : Bounds} {Gs : List GTy} : GSubst.ty (bind Dl Gs) = bind Dl (GTy.tys Gs) := by
  rw [GTy.tys_eq_map]
  simp only [GSubst.ty, bind, List.zip_map_right]
  rfl

theorem exprs_mem {v : Value} : forall {vs : List Value}, List.Mem v vs -> List.Mem v.expr (Value.exprs vs)
  | _, .head _ => by simp only [Value.exprs]; exact List.Mem.head _
  | _, .tail _ h => by simp only [Value.exprs]; exact List.Mem.tail _ (exprs_mem h)

theorem uniqList_mem_e {e : Expr} : forall {es : List Expr}, List.Mem e es -> Expr.uniqList es -> e.uniq
  | _, .head _, hu => by simp only [Expr.uniqList] at hu; exact hu.1
  | _, .tail _ h, hu => by simp only [Expr.uniqList] at hu; exact uniqList_mem_e h hu.2

theorem vbindersList_mem_e {e : Expr} {x : VarName} : forall {es : List Expr}, List.Mem e es ->
    List.Mem x e.vbinders -> List.Mem x (Expr.vbindersList es)
  | _, .head _, hx => by simp only [Expr.vbindersList, listMem_iff, List.mem_append]; exact Or.inl hx
  | _, .tail _ h, hx => by simp only [Expr.vbindersList, listMem_iff, List.mem_append]; exact Or.inr (vbindersList_mem_e h hx)


theorem found_tail {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {B : Bounds} {Gall : List GTy}
    {Tt T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value} {vs : List Value}
    (hb : Typing d B ([{ T := Tt, x := this }] ++ ps) e0 T0) (hgok : GOk d B (bind B Gall))
    (hfst : (bind B Gall).map Prod.fst = dom B) (hN' : (this :: ps.map VarDecl.x).Nodup) (hp : ps.length = vs.length)
    (hgs : GSubstDefined (dom B) e0) (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0)
    (hnx : e0.noShadow [] (this :: ps.map VarDecl.x) = true) (ht0 : NoThis e0) (hu0 : e0.uniq)
    (ha' : WFExpr ((e0.gsubst (bind B Gall)).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))))
    (hargs : TypingSeq d [] [] (Value.exprs (v0 :: vs)) (Ty.substList (GSubst.ty (bind B Gall)) (Tt :: ps.map VarDecl.T)))
    (hn : Expr.noShadowList [] [] (Value.exprs (v0 :: vs)) = true)
    (ht : Not (List.Mem this (Expr.vbindersList (Value.exprs (v0 :: vs))))) (hu : Expr.uniqList (Value.exprs (v0 :: vs))) :
    Typing d [] [] ((e0.gsubst (bind B Gall)).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs)))
      (T0.subst (GSubst.ty (bind B Gall))) := by
  have hgt := Typing.gsub hwf hok hd hb (s := bind B Gall) (Xs := []) (xs := this :: ps.map VarDecl.x) hgok
    (fun X hX hm => hgs X hX (by rw [hfst] at hm; exact hm)) (by simpa [gdom] using hN')
    (fun y hy => by simpa [gdom] using hy) hnx ht0 hu0
  have eB : gsubB (bind B Gall) B = [] := by
    simp only [gsubB, Bounds.subst]
    rw [List.filter_eq_nil_iff.mpr]
    . rfl
    . intro b hb
      rw [hfst]
      have hc : (dom B).contains b.X = true := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Bound.X) hb)
      rw [hc]; decide
  rw [eB] at hgt
  have hgd : gdom (gsubG (bind B Gall) ([{ T := Tt, x := this }] ++ ps)) = this :: ps.map VarDecl.x := by
    rw [gdom_gsubG]; simp [gdom]
  have hg1T : (gsubG (bind B Gall) ([{ T := Tt, x := this }] ++ ps)).map VarDecl.T =
      Ty.substList (GSubst.ty (bind B Gall)) (Tt :: ps.map VarDecl.T) := by
    simp only [gsubG, List.singleton_append, List.map_cons, VarDecl.subst, Ty.substList]
    rw [params_T_subst]
  have hnf : ((this :: ps.map VarDecl.x).zip (v0 :: vs)).map Prod.fst = this :: ps.map VarDecl.x :=
    zip_map_fst (by simp [hp])
  have eG : gsub ((this :: ps.map VarDecl.x).zip (v0 :: vs)) (gsubG (bind B Gall) ([{ T := Tt, x := this }] ++ ps)) =
      [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hax : List.Mem a.x (gdom (gsubG (bind B Gall) ([{ T := Tt, x := this }] ++ ps))) :=
      List.mem_map_of_mem (f := VarDecl.x) ha
    rw [hgd, <- hnf] at hax
    have hc := List.contains_iff_mem.mpr hax
    show Not ((!(List.contains _ a.x)) = true)
    rw [hc]; decide
  have hres := Typing.vsub hgt (n := (this :: ps.map VarDecl.x).zip (v0 :: vs)) (Xs := [])
    (xs := this :: ps.map VarDecl.x) (xs' := [])
    (fun x v U h1 h2 => typingSeq_lookup (vs := v0 :: vs) (by rw [hgd]; exact hN') (by rw [hg1T]; exact hargs) x v U
      (by rw [hgd]; exact h1) h2)
    (fun p hp => by
      have hv := exprs_mem (List.of_mem_zip hp).2
      exact And.intro (noShadowList_mem hv hn) (And.intro (fun h => ht (vbindersList_mem_e hv h)) (uniqList_mem_e hv hu)))
    (fun y hy => by rw [hnf]; rw [Expr.vbinders_gsubst] at hy; exact hvs y hy)
    (by rw [hgd]; exact hN')
    (by rw [hgd]; exact fun y hy => hy)
    (by rw [eG]; intro y hy; cases hy)
    (by rw [Expr.noShadow_gsubst]; exact hnx) ha'.2.2.2.2.1
    (by simpa [NoThis, Expr.vbinders_gsubst] using ht0) (by rw [Expr.uniq_gsubst]; exact hu0)
  rwa [eG] at hres

theorem found_body {e0 : Expr} {s : GSubst} {n : VSubst} {Xs : List TVarName} {Delta' : Bounds} {T0 : Ty}
    {m : MethName} {ps : List VarDecl} (ha' : WFExpr ((e0.gsubst s).vsubst n))
    (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0) (hgs : GSubstDefined (Xs ++ dom Delta') e0)
    (hN : (dom Delta').Nodup) (hN' : (this :: ps.map VarDecl.x).Nodup) :
    e0.noShadow [] (this :: ps.map VarDecl.x) = true /\ NoThis e0 /\ e0.uniq /\
    (Method.mk Delta' T0 m ps e0).noShadow [] [] = true /\ NoThisM (Method.mk Delta' T0 m ps e0) /\
    (Method.mk Delta' T0 m ps e0).uniq := by
  have hn0 := (Expr.vsubst_back _ _).2.2 _ _ ha'.2.2.2.2.1
  rw [Expr.noShadow_gsubst] at hn0
  have hnx : e0.noShadow [] (this :: ps.map VarDecl.x) = true :=
    Expr.noShadow_scope hn0 (fun y hy hm => absurd hm (hvs y hy))
  have ht0 : NoThis e0 := by
    have := noThis_of_vsubst (WFExpr.noThis ha')
    simpa [NoThis, Expr.vbinders_gsubst] using this
  have hu0 : e0.uniq := by
    have := (Expr.vsubst_back _ _).2.1 (WFExpr.uniq ha')
    rwa [Expr.uniq_gsubst] at this
  have hnD : e0.noShadow (dom Delta') (this :: ps.map VarDecl.x) = true :=
    Expr.noShadow_tscope hnx (fun X hX hm => absurd (by simp only [listMem_iff, List.mem_append] at hm |-; exact Or.inr hm)
      (hgs X hX))
  refine ⟨hnx, ht0, hu0, ?_, ?_, And.intro hN (And.intro (List.nodup_cons.mp hN').2 hu0)⟩
  . simp only [Method.noShadow, List.nil_append, List.cons_append, Bool.and_eq_true]
    exact And.intro (And.intro (by simp) (by simp)) hnD
  . simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or]
    exact And.intro (List.nodup_cons.mp hN').1 ht0

theorem pres_simpleFound' {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {D : Dec} {M : Method}
    {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value} {Gs Gs' : List GTy}
    {vs : List Value} {T : Ty} (hD : Declared d (.dec D)) (hM : List.Mem M D.Ms)
    (hF : FreshM M (.mk Delta' T0 m ps e0)) (hG : Gs.length = D.bounds.length) (hG' : Gs'.length = Delta'.length)
    (hN : (dom D.bounds ++ dom Delta').Nodup) (hN' : (this :: ps.map VarDecl.x).Nodup)
    (hp : ps.length = vs.length) (hgs : GSubstDefined (dom D.bounds ++ dom Delta') e0)
    (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0)
    (ha : WFExpr (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)))
    (ha' : WFExpr ((e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
      ((this :: ps.map VarDecl.x).zip (v0 :: vs))))
    (h : Typing d [] [] (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
      ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  have hwm := WFDecls.method hwf hD.dec_mem hM
  rcases found_body (T0 := T0) (m := m) ha' hvs hgs (nodup_append_right hN) hN' with ⟨hnx, ht0, hu0, hnM', htM', huM'⟩
  rcases inv_super h rfl with ⟨⟨D1, Ts, D0, Ts0, Delta1, T0o, pso, body, T0', Ts'⟩, hw⟩
  have ann := hw.ann
  simp only [Ty.cls.injEq] at ann
  have eD : D = D1 := by
    have e := Declared.unique hwf hD hw.decl (by simp only [K.name]; exact ann.1)
    injection e
  subst eD
  have eTs := ann.2
  subst eTs
  rcases hw.meth with ⟨k, hk, hkn, hkM⟩
  have ek := Declared.unique hwf hk hw.decl0 hkn
  subst ek
  rcases dec_override hwf hok hd hD hM hw.decl0 (by rw [gtys_length]; exact hG) hw.sub with ⟨Us, hUs, hO, hUf⟩
  have hO' := OverrideOkM.ren (rv := []) (rt := []) hwf hok hO hF.1
    (fun X hX hm => Method.noShadow_dom hwm.2.2 X hm (hUf X hX)) hwm.1
  rw [Ty.renList_id (fun _ _ => rn_nil)] at hO'
  generalize hTT : Ty.cls D0.C Us = TT at hO'
  cases hO' with
  | absent h1 h2 =>
    simp only [Ty.cls.injEq] at hTT
    have e := Declared.unique hwf hw.decl0 h1 (by simp only [K.name]; exact hTT.1)
    cases e
    exact absurd (List.mem_map_of_mem (f := Method.name) hkM) h2
  | loc h1 =>
    simp only [Ty.cls.injEq] at hTT
    exact absurd (Declared.dec_loc hwf hw.decl0 h1 hTT.1) id
  | @dec D2 Us2 _ _ _ _ _ Do T0x psx ex h1 h2 h3 h4 h5 h6 =>
    simp only [Ty.cls.injEq] at hTT
    have e := Declared.unique hwf hw.decl0 h1 (by simp only [K.name]; exact hTT.1)
    cases e
    have eU := hTT.2
    subst eU
    have eM := names_unique (Declared.namesNodup hwf hw.decl0) h2 hkM rfl
    simp only [Method.mk.injEq] at eM
    rcases eM with ⟨eM1, eM2, _, eM4, _⟩
    subst eM1 eM2 eM4
    have hsg : GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs')) =
        (dom D.bounds ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs') := by
      rw [gsubst_ty_bind, GTy.tys_eq_map, GTy.tys_eq_map, GTy.tys_eq_map, List.map_append]
      simp only [bind, dom_append]
    have hlenF : (GTy.tys Gs ++ GTy.tys Gs').length = (dom D.bounds ++ dom Delta').length := by
      simp [gtys_length, hG, hG', dom]
    have hvF := vars_subst hN hlenF
    rw [<- hsg, vars_append, substList_app] at hvF
    have hv1 := List.append_inj hvF (by simp [substList_length, vars, dom, gtys_length, hG])
    have hcomp1 : forall L, (forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom D.bounds)) ->
        Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) L =
          Ty.substList (bind D.bounds (GTy.tys Gs)) L := by
      intro L hL
      conv => lhs; rw [<- substList_bind_vars_id hL]
      rw [substList_bind_comp (by simp [vars, dom]) hL, hv1.1]
    have hUt : Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) Us = Ts0 := by
      rw [hcomp1 Us hUf]; exact hUs.symm
    have hcl0 := declMeth_closed hwf hok hw.decl0 hkM
    simp only [K.gvars, <- dom_append] at hcl0
    have hlen0 : (Us ++ vars (dom Delta')).length = (D0.bounds ++ Do).length := by simp [h3, h4, vars, dom]
    have hcomp2 : forall L, (forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom (D0.bounds ++ Do))) ->
        Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs')))
          (Ty.substList (bind (D0.bounds ++ Do) (Us ++ vars (dom Delta'))) L) =
          Ty.substList (bind (D0.bounds ++ Do) (Ts0 ++ GTy.tys Gs')) L := by
      intro L hL
      rw [substList_bind_comp hlen0 hL, substList_app, hUt, hv1.2]
    have hsig : Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) (T0 :: ps.map VarDecl.T) =
        T0' :: Ts' := by
      rw [<- h6, hcomp2 _ hcl0.2]; exact hw.sig.symm
    have hcod : Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) (cod Delta') =
        Ty.substList (bind (D0.bounds ++ Do) (Ts0 ++ GTy.tys Gs')) (cod Do) := by
      rw [<- h5, hcomp2 _ hcl0.1]
    have hmo := (hok D hD.dec_mem).2.2.1 M hM
    have env : REnv [] [] D.bounds D.bounds [{ T := .cls D.C (vars (dom D.bounds)), x := this }]
        [{ T := .cls D.C (vars (dom D.bounds)), x := this }] (dom D.bounds) [this] [this] :=
      { bD := fun b hb => by rw [rn_nil, Ty.ren_id (fun _ _ => rn_nil)]; exact hb
        dX := fun X hX => hX
        dT := fun b hb X hX => Kind.ftv ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb)) X hX
        g := fun z U hl => by rw [rn_nil, Ty.ren_id (fun _ _ => rn_nil)]; exact hl
        gT := fun y hy X hX => by
          cases hy with
          | head => exact ftv_vars (by simpa [Ty.ftv] using hX)
          | tail _ h => cases h
        gN := by simp [gdom]
        gx := fun y hy => hy
        gx' := fun y hy => hy
        kv := fun _ h => by cases h }
    have hmo' := MethodOk.ren hwf hok hd hmo hF.1 env hwm.2.2 hnM' hwm.2.1 htM' hwm.1 huM'
    have hmi := methodOk_inv hmo'
    have hlook : forall b, List.Mem b (D.bounds ++ Delta') -> forall U,
        List.Mem (b.X, U) ((dom D.bounds ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs')) ->
        (Ty.var b.X).subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) = U := by
      intro b _ U hm
      rw [hsg]
      simp only [Ty.subst, lookup_zip_nodup hN hm, Option.getD_some]
    have hbF : forall b, List.Mem b (D.bounds ++ Delta') ->
        Sub d [] ((Ty.var b.X).subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))))
          (b.T.subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs')))) /\
        Kind d [] ((Ty.var b.X).subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs')))) := by
      intro b hb
      have hb' := hb
      simp only [listMem_iff, List.mem_append] at hb'
      rcases hb' with hb1 | hb1
      . have hka := (kind_dec_args hwf hD hw.kind).2 b hb1
        have hbT : forall X, List.Mem X (Ty.ftvList [b.T]) -> List.Mem X (dom D.bounds) := by
          intro X hX
          simp only [Ty.ftvList, List.append_nil] at hX
          exact Kind.ftv ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb1)) X hX
        have hbX : forall X, List.Mem X (Ty.ftvList [Ty.var b.X]) -> List.Mem X (dom D.bounds) := by
          intro X hX
          cases hX with
          | head => exact List.mem_map_of_mem (f := Bound.X) hb1
          | tail _ h => cases h
        have e1 := hcomp1 [b.T] hbT
        have e2 := hcomp1 [Ty.var b.X] hbX
        simp only [Ty.substList, List.cons.injEq] at e1 e2
        rw [e1.1, e2.1]
        exact hka
      . have hss := hw.subs
        rw [<- hcod] at hss
        rcases bounds_sat_aux (by rw [gtys_length]; exact hG') hss hw.kinds b hb1 with ⟨U, hU⟩
        have hm : List.Mem (b.X, U) ((dom D.bounds ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs')) := by
          rw [List.zip_append (by simp [gtys_length, hG, dom])]
          simp only [listMem_iff, List.mem_append]
          exact Or.inr hU.1
        rw [hlook b hb U hm]
        exact hU.2
    have hgok : GOk d (D.bounds ++ Delta') (bind (D.bounds ++ Delta') (Gs ++ Gs')) := by
      intro b hb G hl
      have e := var_gsubst_some hl
      have hk := hbF b hb
      rw [e] at hk
      refine And.intro hk.1 (And.intro hk.2 ?_)
      have hKb : Kind d (D.bounds ++ Delta') b.T := by
        simp only [listMem_iff, List.mem_append] at hb
        rcases hb with hb | hb
        . exact Kind.mono (fun x hx => by simp only [listMem_iff, List.mem_append]; exact Or.inl hx)
            ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb))
        . exact hmi.1 b.T (List.mem_map_of_mem (f := Bound.T) hb)
      exact Kind.subst hd (fun b hb => (hbF b hb).1) (fun b hb => (hbF b hb).2) hKb
    have hfst : (bind (D.bounds ++ Delta') (Gs ++ Gs')).map Prod.fst = dom (D.bounds ++ Delta') :=
      bind_fst (by simp [hG, hG'])
    have hs2 := hsig
    simp only [Ty.substList, List.cons.injEq] at hs2
    have hres := found_tail hwf hok hd hmi.2.2 hgok hfst hN' hp (by rw [dom_append]; exact hgs) hvs hnx ht0 hu0 ha'
      (by simp only [Ty.substList, Ty.subst]; rw [hv1.1, hs2.2]; exact hw.args) ha.2.2.2.2.1 (WFExpr.noThis ha)
      (WFExpr.uniq ha)
    rw [hs2.1] at hres
    exact hw.up.typing hres

end Funnelling.High
