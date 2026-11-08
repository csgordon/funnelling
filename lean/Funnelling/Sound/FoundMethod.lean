import Funnelling.Sound.Overriding

open Funnelling.SoundSimp

namespace Funnelling

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
      have hv := Value.mem_exprs (List.of_mem_zip hp).2
      exact And.intro (Expr.noShadowList_mem hv hn) (And.intro (fun h => ht (Expr.mem_vbindersList hv h)) (Expr.uniqList_mem hv hu)))
    (fun y hy => by rw [hnf]; rw [Expr.vbinders_gsubst] at hy; exact hvs y hy)
    (by rw [hgd]; exact hN')
    (by rw [hgd]; exact fun y hy => hy)
    (by rw [eG]; intro y hy; cases hy)
    (by rw [Expr.noShadow_gsubst]; exact hnx) ha'.2.2.2.2.1
    (by simpa [NoThis, Expr.vbinders_gsubst] using ht0) (by rw [Expr.uniq_gsubst]; exact hu0)
  rwa [eG] at hres

structure Found (M : Method) (B0 Delta' : Bounds) (T0 : Ty) (m : MethName) (ps : List VarDecl) (e0 : Expr)
    (Gs Gs' : List GTy) (v0 : Value) (vs : List Value) : Prop where
  fresh : FreshM M (.mk Delta' T0 m ps e0)
  lenT : Gs'.length = Delta'.length
  lenV : ps.length = vs.length
  nodupT : (dom B0 ++ dom Delta').Nodup
  nodupV : (this :: ps.map VarDecl.x).Nodup
  gdef : GSubstDefined (dom B0 ++ dom Delta') e0
  vdef : VSubstDefined (this :: ps.map VarDecl.x) e0
  wf : WFExpr ((e0.gsubst (bind (B0 ++ Delta') (Gs ++ Gs'))).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs)))

namespace Found

variable {M : Method} {B0 Delta' : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl} {e0 : Expr}
  {Gs Gs' : List GTy} {v0 : Value} {vs : List Value} (f : Found M B0 Delta' T0 m ps e0 Gs Gs' v0 vs)
include f

theorem noShadow : e0.noShadow [] (this :: ps.map VarDecl.x) = true := by
  have hn0 := (Expr.vsubst_back _ _).2.2 _ _ f.wf.2.2.2.2.1
  rw [Expr.noShadow_gsubst] at hn0
  exact Expr.noShadow_mono hn0 (fun _ _ hX => hX) (fun y hy hm => absurd hm (f.vdef y hy))

theorem noThis : NoThis e0 := by
  have := noThis_of_vsubst (WFExpr.noThis f.wf)
  simpa [NoThis, Expr.vbinders_gsubst] using this

theorem uniq : e0.uniq := by
  have := (Expr.vsubst_back _ _).2.1 (WFExpr.uniq f.wf)
  rwa [Expr.uniq_gsubst] at this

theorem methNoShadow : (Method.mk Delta' T0 m ps e0).noShadow [] [] = true := by
  simp only [Method.noShadow, List.nil_append, List.cons_append, Bool.and_eq_true]
  refine And.intro (And.intro (by simp) (by simp)) (Expr.noShadow_mono f.noShadow (fun X hX hm => ?_) (fun _ _ hy => hy))
  exact absurd (by simp only [listMem_iff, List.mem_append] at hm |-; exact Or.inr hm) (f.gdef X hX)

theorem methNoThis : NoThisM (Method.mk Delta' T0 m ps e0) := by
  simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or]
  exact And.intro (List.nodup_cons.mp f.nodupV).1 f.noThis

theorem methUniq : (Method.mk Delta' T0 m ps e0).uniq :=
  And.intro (nodup_append_right f.nodupT) (And.intro (List.nodup_cons.mp f.nodupV).2 f.uniq)

end Found

theorem pres_simpleFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {D : Dec} {M : Method}
    {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value} {Gs Gs' : List GTy}
    {vs : List Value} {T : Ty} (hD : Declared d (.dec D)) (hM : List.Mem M D.Ms) (hG : Gs.length = D.bounds.length)
    (f : Found M D.bounds Delta' T0 m ps e0 Gs Gs' v0 vs)
    (ha : WFExpr (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)))
    (h : Typing d [] [] (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
      ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  have hwm := WFDecls.method hwf hD.dec_mem hM
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
  have hO' := OverrideOkM.ren (rv := []) (rt := []) hwf hok hO f.fresh.1
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
      simp [gtys_length, hG, f.lenT, dom]
    have hvF := vars_subst f.nodupT hlenF
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
    have hmo' := MethodOk.ren hwf hok hd hmo f.fresh.1 env hwm.2.2 f.methNoShadow hwm.2.1 f.methNoThis hwm.1 f.methUniq
    have hmi := methodOk_inv hmo'
    have hlook : forall b, List.Mem b (D.bounds ++ Delta') -> forall U,
        List.Mem (b.X, U) ((dom D.bounds ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs')) ->
        (Ty.var b.X).subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) = U := by
      intro b _ U hm
      rw [hsg]
      simp only [Ty.subst, lookup_zip_nodup f.nodupT hm, Option.getD_some]
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
        rcases bounds_sat_aux (by rw [gtys_length]; exact f.lenT) hss hw.kinds b hb1 with ⟨U, hU⟩
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
      bind_fst (by simp [hG, f.lenT])
    have hs2 := hsig
    simp only [Ty.substList, List.cons.injEq] at hs2
    have hres := found_tail hwf hok hd hmi.2.2 hgok hfst f.nodupV f.lenV (by rw [dom_append]; exact f.gdef) f.vdef
      f.noShadow f.noThis f.uniq f.wf (by simp only [Ty.substList, Ty.subst]; rw [hv1.1, hs2.2]; exact hw.args)
      ha.2.2.2.2.1 (WFExpr.noThis ha) (WFExpr.uniq ha)
    rw [hs2.1] at hres
    exact hw.up.typing hres

theorem pres_innerFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {C C' : ClassName}
    {Ms : List Method} {M : Method} {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr}
    {v0 : Value} {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} {T : Ty} (hv : v0 = Value.newLocal C Gs C' Gs'' vs0 Ms)
    (hM : List.Mem M Ms) (f : Found M [] Delta' T0 m ps e0 [] Gs' v0 vs)
    (ha : WFExpr (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)))
    (h : Typing d [] [] (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  have hN : (dom Delta').Nodup := f.nodupT
  have han := ha.2.2.2.2.1
  simp only [Expr.noShadow, Bool.and_eq_true] at han
  have hat := WFExpr.noThis ha
  simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at hat
  have hau := WFExpr.uniq ha
  have hv0n := han.1
  have hv0t := hat.1
  have hv0u := hau.1
  rw [hv] at hv0n hv0t hv0u
  simp only [Value.expr, Expr.noShadow, Bool.and_eq_true, Expr.vbinders, List.mem_append, not_or,
    Expr.uniq] at hv0n hv0t hv0u
  have hnM : M.noShadow [] [] = true := by
    have := Method.noShadowList_mem hM hv0n.2
    simpa using this
  have htM : NoThisM M := fun h => hv0t.2 (Method.mem_vbindersList hM h)
  have huM : M.uniq := Method.uniqList_mem hM hv0u.2
  rcases inv_call h rfl with ⟨⟨C0, Ts0, Delta0, Ts2, Delta1, T0c, psc, body, T0', Ts'⟩, hw⟩
  have vt := value_typing hwf hw.ty0
  have hsv : Sub d [] (typeOf v0) (.cls C0 Ts0) := by
    rcases vt.1 with e | e
    . rw [e]; exact Sub.subRefl
    . exact e.1
  have hk0 : Kind d [] (.cls C0 Ts0) := kind_chain hwf hok hd (by rw [hv] at vt; exact vt.2.2) (by rw [hv] at hsv; exact hsv)
  have hty0 := vt.2.1
  rw [hv] at hsv hty0
  rcases inv_local hty0 rfl with ⟨w2, hw2⟩
  have hD2 := pairing_ground_nil hw2.pair
  have hmeth := hw2.meths M hM
  rw [hD2, abs_ground] at hmeth
  have hover := hw2.over
  rw [hD2] at hover
  rcases consistent_unfold hw2.cons with ⟨Fs', Ts'd, es', Ms'd, hcd, _, hcts, _, hcov⟩
  have hO : OverrideOkM d (.cls C0 Ts0) M := by
    rcases Sub.loc_step hwf hcd hsv with e | e
    . simp only [Ty.cls.injEq] at e
      rcases e with ⟨e1, e2⟩
      subst e1 e2
      have := hcov M hM
      rwa [abs_ground] at this
    . have hs2 := e.2
      simp only [Ty.subst] at hs2
      rw [abs_ground] at hcts
      rw [<- hcts] at hs2
      exact hover M C0 Ts0 hM hs2
  have hTs0 : forall X, List.Mem X (Ty.ftvList Ts0) -> False := fun X hX => by
    have := Kind.ftv hk0 X (by simpa [Ty.ftv] using hX)
    cases this
  have hO' := OverrideOkM.ren (rv := []) (rt := []) hwf hok hO f.fresh.1 (fun X hX _ => hTs0 X hX) huM
  rw [Ty.renList_id (fun _ _ => rn_nil)] at hO'
  rcases found_sig hwf hw.scope hw.meth hw.len2 hO' with ⟨eT2, h4, h5, h6⟩
  have hsg : GSubst.ty (bind Delta' Gs') = (dom Delta').zip (GTy.tys Gs') := by rw [gsubst_ty_bind]; rfl
  have hv1 : Ty.substList (GSubst.ty (bind Delta' Gs')) (vars (dom Delta')) = GTy.tys Gs' := by
    rw [hsg]; exact vars_subst hN (by simp [gtys_length, f.lenT, dom])
  have hT2 : Ty.substList (GSubst.ty (bind Delta' Gs')) Ts2 = Ts2 := by
    apply Ty.substList_id
    intro X hX
    have e : Ts2 = Ts0 := eT2
    rw [e] at hX
    exact absurd hX (fun h => hTs0 X h)
  have hcl0 := methodIn_closed hwf hok hw.scope hw.meth
  have hlen0 : (Ts2 ++ vars (dom Delta')).length = (Delta0 ++ Delta1).length := by simp [hw.len2, h4, vars, dom]
  have hcomp2 : forall L, (forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom (Delta0 ++ Delta1))) ->
      Ty.substList (GSubst.ty (bind Delta' Gs'))
        (Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ vars (dom Delta'))) L) =
        Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ GTy.tys Gs')) L := by
    intro L hL
    rw [substList_bind_comp hlen0 hL, substList_app, hT2, hv1]
  have hsig : Ty.substList (GSubst.ty (bind Delta' Gs')) (T0 :: ps.map VarDecl.T) = T0' :: Ts' := by
    rw [<- h6, hcomp2 _ hcl0.1]; exact hw.sig.symm
  have hcod : Ty.substList (GSubst.ty (bind Delta' Gs')) (cod Delta') =
      Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ GTy.tys Gs')) (cod Delta1) := by
    rw [<- h5, hcomp2 _ hcl0.2]
  have env : REnv [] [] [] [] [{ T := .cls C (GTy.tys Gs), x := this }]
      [{ T := .cls C (GTy.tys Gs), x := this }] [] [this] [this] :=
    { bD := fun _ h => by cases h
      dX := fun _ h => by cases h
      dT := fun _ h => by cases h
      g := fun z U hl => by rw [rn_nil, Ty.ren_id (fun _ _ => rn_nil)]; exact hl
      gT := fun y hy X hX => by
        cases hy with
        | head => simp [Ty.ftv, GTy.ftv_tys] at hX
        | tail _ h => cases h
      gN := by simp [gdom]
      gx := fun y hy => hy
      gx' := fun y hy => hy
      kv := fun _ h => by cases h }
  have hmeth' : MethodOk d [] [{ T := .cls C (GTy.tys Gs), x := this }] M := by
    simpa [withoutThis, restrict] using hmeth
  have hmo' := MethodOk.ren hwf hok hd hmeth' f.fresh.1 env hnM f.methNoShadow htM f.methNoThis huM f.methUniq
  have hmi := methodOk_inv hmo'
  simp only [List.nil_append] at hmi
  have hbF : forall b, List.Mem b Delta' ->
      Sub d [] ((Ty.var b.X).subst (GSubst.ty (bind Delta' Gs'))) (b.T.subst (GSubst.ty (bind Delta' Gs'))) /\
      Kind d [] ((Ty.var b.X).subst (GSubst.ty (bind Delta' Gs'))) := by
    intro b hb
    have hss := hw.subs
    rw [<- hcod] at hss
    rcases bounds_sat_aux (by rw [gtys_length]; exact f.lenT) hss hw.kinds b hb with ⟨U, hU⟩
    rw [hsg]
    simp only [Ty.subst, lookup_zip_nodup hN hU.1, Option.getD_some]
    rw [<- hsg]
    exact hU.2
  have hgok : GOk d Delta' (bind Delta' Gs') := by
    intro b hb G hl
    have e := var_gsubst_some hl
    have hk := hbF b hb
    rw [e] at hk
    exact And.intro hk.1 (And.intro hk.2 (Kind.subst hd (fun b hb => (hbF b hb).1) (fun b hb => (hbF b hb).2)
      (hmi.1 b.T (List.mem_map_of_mem (f := Bound.T) hb))))
  have hfst : (bind Delta' Gs').map Prod.fst = dom Delta' := bind_fst f.lenT
  have htv0 : Typing d [] [] v0.expr (.cls C (GTy.tys Gs)) := by
    have := vt.2.1
    rw [hv] at this |-
    simpa [typeOf] using this
  have hs2 := hsig
  simp only [Ty.substList, List.cons.injEq] at hs2
  have eg : (Ty.cls C (GTy.tys Gs)).subst (GSubst.ty (bind Delta' Gs')) = Ty.cls C (GTy.tys Gs) :=
    GTy.subst_ty (GTy.cls C Gs)
  have hres := found_tail hwf hok hd hmi.2.2 hgok hfst f.nodupV f.lenV f.gdef f.vdef f.noShadow f.noThis f.uniq f.wf
    (by simp only [Ty.substList]; rw [eg, hs2.2]; exact TypingSeq.cons htv0 hw.args) ha.2.2.2.2.1
    (WFExpr.noThis ha) (WFExpr.uniq ha)
  rw [hs2.1] at hres
  exact hw.up.typing hres

end Funnelling
