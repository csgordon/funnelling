import Funnelling.Sound.Overriding

open Funnelling.SoundSimp

namespace Funnelling

theorem typingSeq_lookup {d : Decls} : forall {g : TypeEnv} {vs : List Value},
    (gdom g).Nodup -> TypingSeq d [] [] (Value.exprs vs) (g.map VarDecl.T) ->
    forall x v U, List.lookup x ((gdom g).zip vs) = some v -> g.lookup x = some U -> Typing d [] [] v.expr U
  | [], _, _, _, x, v, U, _, h => by simp [TypeEnv.lookup] at h
  | _ :: _, [], _, h, _, _, _, _, _ => by cases h
  | y :: g, v0 :: vs, hn, h, x, v, U, h1, h2 => by
    cases h with
    | cons ht hts =>
      simp only [gdom, List.map_cons, List.zip_cons_cons] at h1 hn
      by_cases e : x = y.x
      . subst e
        rw [lookup_cons_eq] at h1
        cases h1
        simp only [TypeEnv.lookup, List.find?_cons, beq_self_eq_true, Option.map_some] at h2
        cases h2
        exact ht
      . rw [lookup_cons_ne e] at h1
        have hb : (y.x == x) = false := by simpa using fun h => e h.symm
        simp only [TypeEnv.lookup, List.find?_cons, hb] at h2
        exact typingSeq_lookup (List.nodup_cons.mp hn).2 hts x v U h1 h2

theorem gsubst_ty_bind {Dl : Bounds} {Gs : List GTy} : GSubst.ty (bind Dl Gs) = bind Dl (GTy.tys Gs) := by
  rw [GTy.tys_eq_map]
  simp only [GSubst.ty, bind, List.zip_map_right]
  rfl

namespace Found

variable {M : Method} {B0 Delta' : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl} {e0 : Expr}
  {Gs Gs' : List GTy} {v0 : Value} {vs : List Value} (f : Found M B0 Delta' T0 m ps e0 Gs Gs' v0 vs)
include f

theorem noShadow : e0.noShadow [] (this :: ps.map VarDecl.x) = true := by
  have hn0 := (Expr.vsubst_back _ _).2.2 _ _ f.wf.noShadow
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

omit f in theorem subst_eq :
    GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs')) = (dom B0 ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs') := by
  rw [gsubst_ty_bind, GTy.tys_eq_map, GTy.tys_eq_map, GTy.tys_eq_map, List.map_append]
  simp only [bind, dom_append]

theorem subst_vars (hG : Gs.length = B0.length) :
    Ty.substList (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))) (vars (dom B0)) = GTy.tys Gs /\
    Ty.substList (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))) (vars (dom Delta')) = GTy.tys Gs' := by
  have hv := vars_subst f.nodupT (Us := GTy.tys Gs ++ GTy.tys Gs') (by simp [gtys_length, hG, f.lenT, dom])
  rw [<- subst_eq, vars_append, substList_app] at hv
  exact List.append_inj hv (by simp [substList_length, vars, dom, gtys_length, hG])

theorem sig (hG : Gs.length = B0.length) {Delta0 Do : Bounds} {Us Ts0 : List Ty}
    (hUs : Ty.substList (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))) Us = Ts0)
    (hlU : Us.length = Delta0.length) (hlD : Delta'.length = Do.length) {L : List Ty}
    (hL : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom (Delta0 ++ Do))) :
    Ty.substList (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs')))
      (Ty.substList (bind (Delta0 ++ Do) (Us ++ vars (dom Delta'))) L) =
      Ty.substList (bind (Delta0 ++ Do) (Ts0 ++ GTy.tys Gs')) L := by
  rw [substList_bind_comp (by simp [hlU, hlD, vars, dom]) hL, substList_app, hUs, (f.subst_vars hG).2]

theorem typing {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) (hG : Gs.length = B0.length) {Tt : Ty}
    (hmo : MethodOk d B0 [{ T := Tt, x := this }] (.mk Delta' T0 m ps e0))
    (hb0 : forall b, List.Mem b B0 ->
      Sub d [] ((Ty.var b.X).subst (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))))
        (b.T.subst (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs')))) /\
      Kind d [] ((Ty.var b.X).subst (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs')))))
    (hK0 : forall b, List.Mem b B0 -> Kind d (B0 ++ Delta') b.T) {T0' : Ty} {Ts' : List Ty}
    (hsig : Ty.substList (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))) (T0 :: ps.map VarDecl.T) = T0' :: Ts')
    (hsubs : SubSeq d [] (GTy.tys Gs') (Ty.substList (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))) (cod Delta')))
    (hkinds : KindSeq d [] (GTy.tys Gs'))
    (hargs : TypingSeq d [] [] (Value.exprs (v0 :: vs)) (Tt.subst (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))) :: Ts'))
    (hn : Expr.noShadowList [] [] (Value.exprs (v0 :: vs)) = true)
    (ht : Not (List.Mem this (Expr.vbindersList (Value.exprs (v0 :: vs))))) (hu : Expr.uniqList (Value.exprs (v0 :: vs))) :
    Typing d [] [] ((e0.gsubst (bind (B0 ++ Delta') (Gs ++ Gs'))).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T0' := by
  have hmi := methodOk_inv hmo
  have hfst : (bind (B0 ++ Delta') (Gs ++ Gs')).map Prod.fst = dom (B0 ++ Delta') := bind_fst (by simp [hG, f.lenT])
  have hgok : GOk d (B0 ++ Delta') (bind (B0 ++ Delta') (Gs ++ Gs')) := by
    refine GOk.of_bounds hd (fun b hb => ?_) (fun b hb => ?_)
    . rcases List.mem_append.mp hb with hb | hb
      . exact hb0 b hb
      rcases bounds_sat_aux (by rw [gtys_length]; exact f.lenT) hsubs hkinds b hb with ⟨U, hU⟩
      have hm : List.Mem (b.X, U) ((dom B0 ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs')) := by
        rw [List.zip_append (by simp [gtys_length, hG, dom])]
        exact List.mem_append_right _ hU.1
      have e : (Ty.var b.X).subst (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))) = U := by
        rw [subst_eq]
        simp only [Ty.subst, lookup_zip_nodup f.nodupT hm, Option.getD_some]
      rw [e]
      exact hU.2
    . rcases List.mem_append.mp hb with hb | hb
      . exact hK0 b hb
      exact hmi.1 b.T (List.mem_map_of_mem (f := Bound.T) hb)
  have hgt := Typing.gsub hwf hok hd hmi.2.2 (s := bind (B0 ++ Delta') (Gs ++ Gs')) (Xs := []) (xs := this :: ps.map VarDecl.x)
    hgok (fun X hX hm => f.gdef X hX (by rw [hfst, dom_append] at hm; exact hm)) (by simpa [gdom] using f.nodupV)
    (fun y hy => by simpa [gdom] using hy) f.noShadow f.noThis f.uniq
  have eB : gsubB (bind (B0 ++ Delta') (Gs ++ Gs')) (B0 ++ Delta') = [] := by
    simp only [gsubB, Bounds.subst]
    rw [List.filter_eq_nil_iff.mpr]
    . rfl
    . intro b hb
      rw [hfst]
      have hc : (dom (B0 ++ Delta')).contains b.X = true := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Bound.X) hb)
      rw [hc]; decide
  rw [eB] at hgt
  have hgd : gdom (gsubG (bind (B0 ++ Delta') (Gs ++ Gs')) ([{ T := Tt, x := this }] ++ ps)) = this :: ps.map VarDecl.x := by
    rw [gdom_gsubG]; simp [gdom]
  have hg1T : (gsubG (bind (B0 ++ Delta') (Gs ++ Gs')) ([{ T := Tt, x := this }] ++ ps)).map VarDecl.T =
      Tt.subst (GSubst.ty (bind (B0 ++ Delta') (Gs ++ Gs'))) :: Ts' := by
    simp only [gsubG, List.singleton_append, List.map_cons, VarDecl.subst]
    rw [params_T_subst]
    simp only [Ty.substList, List.cons.injEq] at hsig
    rw [hsig.2]
  have hnf : ((this :: ps.map VarDecl.x).zip (v0 :: vs)).map Prod.fst = this :: ps.map VarDecl.x :=
    zip_map_fst (by simp [f.lenV])
  have eG : gsub ((this :: ps.map VarDecl.x).zip (v0 :: vs)) (gsubG (bind (B0 ++ Delta') (Gs ++ Gs')) ([{ T := Tt, x := this }] ++ ps)) =
      [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hax : List.Mem a.x (gdom (gsubG (bind (B0 ++ Delta') (Gs ++ Gs')) ([{ T := Tt, x := this }] ++ ps))) :=
      List.mem_map_of_mem (f := VarDecl.x) ha
    rw [hgd, <- hnf] at hax
    have hc := List.contains_iff_mem.mpr hax
    show Not ((!(List.contains _ a.x)) = true)
    rw [hc]; decide
  have hres := Typing.vsub hgt (n := (this :: ps.map VarDecl.x).zip (v0 :: vs)) (Xs := [])
    (xs := this :: ps.map VarDecl.x) (xs' := [])
    (fun x v U h1 h2 => typingSeq_lookup (vs := v0 :: vs) (by rw [hgd]; exact f.nodupV) (by rw [hg1T]; exact hargs) x v U
      (by rw [hgd]; exact h1) h2)
    (fun p hp => by
      have hv := Value.mem_exprs (List.of_mem_zip hp).2
      exact And.intro (Expr.noShadowList_mem hv hn) (And.intro (fun h => ht (Expr.mem_vbindersList hv h)) (Expr.uniqList_mem hv hu)))
    (fun y hy => by rw [hnf]; rw [Expr.vbinders_gsubst] at hy; exact f.vdef y hy)
    (by rw [hgd]; exact f.nodupV)
    (by rw [hgd]; exact fun y hy => hy)
    (by rw [eG]; intro y hy; cases hy)
    (by rw [Expr.noShadow_gsubst]; exact f.noShadow) f.wf.noShadow
    (by simpa [NoThis, Expr.vbinders_gsubst] using f.noThis) (by rw [Expr.uniq_gsubst]; exact f.uniq)
  rw [eG] at hres
  simp only [Ty.substList, List.cons.injEq] at hsig
  rw [hsig.1] at hres
  exact hres

end Found

theorem pres_simpleFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {D : Dec} {M : Method}
    {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value} {Gs Gs' : List GTy}
    {vs : List Value} {T : Ty} (hD : Declared d (.dec D)) (hM : List.Mem M D.Ms) (hG : Gs.length = D.Delta.length)
    (f : Found M D.Delta Delta' T0 m ps e0 Gs Gs' v0 vs)
    (ha : WFExpr (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)))
    (h : Typing d [] [] (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind (D.Delta ++ Delta') (Gs ++ Gs'))).vsubst
      ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  have hwm := WFDecls.method hwf hD.dec_mem hM
  rcases inv_super h rfl with ⟨⟨D1, Ts, D0, Ts0, Delta1, T0o, pso, body, T0', Ts'⟩, hw⟩
  have ann := hw.ann
  simp only [Ty.cls.injEq] at ann
  have eD : D = D1 := by
    have e := Declared.unique hwf hD hw.decl (by simp only [ClassDecl.name]; exact ann.1)
    injection e
  subst eD
  have eTs := ann.2
  subst eTs
  rcases dec_override hwf hok hd hD hM hw.decl0 (by rw [gtys_length]; exact hG) hw.sub with ⟨Us, hUs, hO, hUf⟩
  have hO' := OverrideOkM.ren (rv := []) (rt := []) hwf hok hO f.fresh.1
    (fun X hX hm => Method.noShadow_dom hwm.2.2 X hm (hUf X hX)) hwm.1
  rw [Ty.renList_id (fun _ _ => rn_nil)] at hO'
  have h3 : Us.length = D0.Delta.length := by rw [<- hw.len0, hUs, substList_length]
  rcases found_sig hwf (Scope.dec hw.decl0) hw.meth h3 hO' with ⟨_, h4, h5, h6⟩
  have hv1 := f.subst_vars hG
  have hcomp1 : forall L, (forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom D.Delta)) ->
      Ty.substList (GSubst.ty (bind (D.Delta ++ Delta') (Gs ++ Gs'))) L =
        Ty.substList (bind D.Delta (GTy.tys Gs)) L := by
    intro L hL
    conv => lhs; rw [<- substList_bind_vars_id hL]
    rw [substList_bind_comp (by simp [vars, dom]) hL, hv1.1]
  have hUt : Ty.substList (GSubst.ty (bind (D.Delta ++ Delta') (Gs ++ Gs'))) Us = Ts0 := by
    rw [hcomp1 Us hUf]; exact hUs.symm
  have hcl0 := methodIn_closed hwf hok (Scope.dec (Ts := Us) hw.decl0) hw.meth
  have hmo := (hok D hD.dec_mem).2.2.1 M hM
  have env : REnv [] [] D.Delta D.Delta [{ T := .cls D.C (vars (dom D.Delta)), x := this }]
      [{ T := .cls D.C (vars (dom D.Delta)), x := this }] (dom D.Delta) [this] [this] :=
    REnv.refl (fun b hb X hX => Kind.ftv ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb)) X hX)
      (fun X hX => ftv_vars (by simpa [Ty.ftv] using hX))
  have hmo' := MethodOk.ren hwf hok hd hmo f.fresh.1 env hwm.2.2 f.methNoShadow hwm.2.1 f.methNoThis hwm.1 f.methUniq
  have hb0 : forall b, List.Mem b D.Delta ->
      Sub d [] ((Ty.var b.X).subst (GSubst.ty (bind (D.Delta ++ Delta') (Gs ++ Gs'))))
        (b.T.subst (GSubst.ty (bind (D.Delta ++ Delta') (Gs ++ Gs')))) /\
      Kind d [] ((Ty.var b.X).subst (GSubst.ty (bind (D.Delta ++ Delta') (Gs ++ Gs')))) := by
    intro b hb
    have hka := (kind_dec_args hwf hD hw.kind).2 b hb
    have hbT : forall X, List.Mem X (Ty.ftvList [b.T]) -> List.Mem X (dom D.Delta) := by
      intro X hX
      simp only [Ty.ftvList, List.append_nil] at hX
      exact Kind.ftv ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb)) X hX
    have hbX : forall X, List.Mem X (Ty.ftvList [Ty.var b.X]) -> List.Mem X (dom D.Delta) := by
      intro X hX
      cases hX with
      | head => exact List.mem_map_of_mem (f := Bound.X) hb
      | tail _ h => cases h
    have e1 := hcomp1 [b.T] hbT
    have e2 := hcomp1 [Ty.var b.X] hbX
    simp only [Ty.substList, List.cons.injEq] at e1 e2
    rw [e1.1, e2.1]
    exact hka
  refine hw.up.typing (f.typing (Ts' := Ts') hwf hok hd hG hmo' hb0 (fun b hb => ?_) ?_ ?_ hw.kinds ?_ ha.noShadow
    (WFExpr.noThis ha) (WFExpr.uniq ha))
  . exact Kind.mono (fun x hx => List.mem_append_left _ hx) ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb))
  . rw [<- h6, f.sig hG hUt h3 h4 hcl0.1]; exact hw.sig.symm
  . rw [<- h5, f.sig hG hUt h3 h4 hcl0.2]; exact hw.subs
  . simp only [Ty.subst]; rw [hv1.1]; exact hw.args

theorem pres_innerFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {C C' : ClassName}
    {Ms : List Method} {M : Method} {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr}
    {v0 : Value} {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} {T : Ty} (hv : v0 = Value.newLocal C Gs C' Gs'' vs0 Ms)
    (hM : List.Mem M Ms) (f : Found M [] Delta' T0 m ps e0 [] Gs' v0 vs)
    (ha : WFExpr (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)))
    (h : Typing d [] [] (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  have hv0 : WFExpr v0.expr := WFExpr.plug (E := .callRecv .hole Gs' m (Value.exprs vs)) ha
  rw [hv] at hv0
  rcases WFExpr.local_method hv0 hM with ⟨hnM, htM, huM, -⟩
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
  obtain rfl : Ts2 = Ts0 := eT2
  have hT2 : Ty.substList (GSubst.ty (bind ([] ++ Delta') ([] ++ Gs'))) Ts2 = Ts2 :=
    Ty.substList_id (fun X hX => absurd hX (hTs0 X))
  have hcl0 := methodIn_closed hwf hok hw.scope hw.meth
  have env : REnv [] [] [] [] [{ T := .cls C (GTy.tys Gs), x := this }]
      [{ T := .cls C (GTy.tys Gs), x := this }] [] [this] [this] :=
    REnv.refl (fun _ h => by cases h) (fun X hX => by simp [Ty.ftv, GTy.ftv_tys] at hX)
  have hmeth' : MethodOk d [] [{ T := .cls C (GTy.tys Gs), x := this }] M := by
    simpa [withoutThis, restrict] using hmeth
  have hmo' := MethodOk.ren hwf hok hd hmeth' f.fresh.1 env hnM f.methNoShadow htM f.methNoThis huM f.methUniq
  have htv0 : Typing d [] [] v0.expr (.cls C (GTy.tys Gs)) := by
    have := vt.2.1
    rw [hv] at this |-
    simpa [typeOf] using this
  refine hw.up.typing (f.typing (Ts' := Ts') hwf hok hd rfl hmo' (fun _ h => by cases h) (fun _ h => by cases h) ?_ ?_ hw.kinds ?_
    ha.noShadow (WFExpr.noThis ha) (WFExpr.uniq ha))
  . rw [<- h6, f.sig rfl hT2 hw.len2 h4 hcl0.1]; exact hw.sig.symm
  . rw [<- h5, f.sig rfl hT2 hw.len2 h4 hcl0.2]; exact hw.subs
  . have eg : (Ty.cls C (GTy.tys Gs)).subst (GSubst.ty (bind ([] ++ Delta') ([] ++ Gs'))) = Ty.cls C (GTy.tys Gs) :=
      GTy.subst_ty (GTy.cls C Gs)
    rw [eg]; exact TypingSeq.cons htv0 hw.args

end Funnelling
