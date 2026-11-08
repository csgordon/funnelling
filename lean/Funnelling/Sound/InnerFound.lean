import Funnelling.Sound.SimpleFound

open Funnelling.SoundSimp

namespace Funnelling

theorem bind_append_len {Dl1 Dl2 : Bounds} {as bs : List Ty} (h : as.length = Dl1.length) :
    bind (Dl1 ++ Dl2) (as ++ bs) = bind Dl1 as ++ bind Dl2 bs := by
  simp only [bind, dom_append]
  rw [List.zip_append (by simp [h, dom])]

theorem found_sig {d : Decls} (hwf : WFDecls d) {C0 : ClassName} {Ts0 : List Ty} {Delta0 : Bounds} {Ts2 : List Ty}
    {Delta1 : Bounds} {T0c : Ty} {m : MethName} {psc : List VarDecl} {body : Expr} {Dp : Bounds} {T0 : Ty}
    {ps : List VarDecl} {e : Expr} (hs : Scope d (.cls C0 Ts0) Delta0 Ts2)
    (hm : MethodIn d (.mk Delta1 T0c m psc body) C0) (hl2 : Ts2.length = Delta0.length)
    (hO : OverrideOkM d (.cls C0 Ts0) (.mk Dp T0 m ps e)) :
    Ts2 = Ts0 /\ Dp.length = Delta1.length /\
      Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ vars (dom Dp))) (cod Delta1) = cod Dp /\
      Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ vars (dom Dp))) (T0c :: psc.map VarDecl.T) =
        T0 :: ps.map VarDecl.T := by
  rcases hm with ⟨k, hk, hkn, hkM⟩
  generalize hTT : Ty.cls C0 Ts0 = TT at hO
  cases hO with
  | absent h1 h2 =>
    simp only [Ty.cls.injEq] at hTT
    have ek := Declared.unique hwf hk h1 (by rw [hkn]; exact hTT.1)
    subst ek
    exact absurd (List.mem_map_of_mem (f := Method.name) hkM) h2
  | @dec D2 _ _ _ _ _ _ Do T0x psx ex h1 h2 h3 h4 h5 h6 =>
    simp only [Ty.cls.injEq] at hTT
    have ek := Declared.unique hwf hk h1 (by rw [hkn]; exact hTT.1)
    subst ek
    have eM := names_unique (Declared.namesNodup hwf h1) h2 hkM rfl
    simp only [Method.mk.injEq] at eM
    rcases eM with ⟨eM1, eM2, _, eM4, _⟩
    subst eM1 eM2 eM4
    have e1 := hTT.1
    have e2 := hTT.2
    subst e1 e2
    have es := Scope.dec_eq hwf h1 hs
    rcases es with ⟨es1, es2⟩
    subst es1 es2
    exact And.intro rfl (And.intro h4 (And.intro h5 h6))
  | @loc C1 Fs C1' Ts1' es1 Ms1 _ _ _ _ _ _ Do T0x psx ex h1 h2 h3 h4 h5 h6 =>
    simp only [Ty.cls.injEq] at hTT
    have ek := Declared.unique hwf hk h1 (by rw [hkn]; exact hTT.1)
    subst ek
    have eM := names_unique (Declared.namesNodup hwf h1) h2 hkM rfl
    simp only [Method.mk.injEq] at eM
    rcases eM with ⟨eM1, eM2, _, eM4, _⟩
    subst eM1 eM2 eM4
    have e1 := hTT.1
    have e2 := hTT.2
    subst e1 e2
    rcases Scope.loc_declared hs with hsd | hsd
    . rcases hsd with ⟨D, hD, hDC, _⟩
      exact absurd (Declared.dec_loc hwf hD h1 hDC) id
    . rcases hsd with ⟨Fs2, C2, Ts2', es2, Ms2, Delta, hdecl, hpair⟩
      have eK := Declared.unique hwf hdecl h1 rfl
      simp only [K.loc.injEq] at eK
      rcases eK with ⟨_, eF, _⟩
      subst eF
      have hall : forall F, List.Mem F Fs2 -> F.isFunnel = true := fun F hF => hwf.2.2.2.2.2.2.2.2.2.2 _ h1.mem F hF
      have eT := pairing_funnels hpair hall
      subst eT
      have hb := bind_eq_bindF (Pairing.dom_eq hpair) hall Ts2
      refine And.intro rfl (And.intro h4 (And.intro ?_ ?_))
      . rw [bind_append_len hl2, hb]; exact h5
      . rw [bind_append_len hl2, hb]; exact h6


theorem pres_innerFound' {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {C C' : ClassName}
    {Ms : List Method} {M : Method} {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr}
    {v0 : Value} {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} {T : Ty} (hv : v0 = Value.newLocal C Gs C' Gs'' vs0 Ms)
    (hM : List.Mem M Ms) (hF : FreshM M (.mk Delta' T0 m ps e0)) (hG' : Gs'.length = Delta'.length)
    (hp : ps.length = vs.length) (hN : (dom Delta').Nodup) (hN' : (this :: ps.map VarDecl.x).Nodup)
    (hgs : GSubstDefined (dom Delta') e0) (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0)
    (ha : WFExpr (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)))
    (ha' : WFExpr ((e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))))
    (h : Typing d [] [] (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  rcases found_body (Xs := []) (T0 := T0) (m := m) ha' hvs hgs hN hN' with ⟨hnx, ht0, hu0, hnM', htM', huM'⟩
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
    have := noShadowListM_mem hM hv0n.2
    simpa using this
  have htM : NoThisM M := fun h => hv0t.2 (vbindersListM_mem hM h)
  have huM : M.uniq := uniqList_mem hM hv0u.2
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
  have hO' := OverrideOkM.ren (rv := []) (rt := []) hwf hok hO hF.1 (fun X hX _ => hTs0 X hX) huM
  rw [Ty.renList_id (fun _ _ => rn_nil)] at hO'
  rcases found_sig hwf hw.scope hw.meth hw.len2 hO' with ⟨eT2, h4, h5, h6⟩
  have hsg : GSubst.ty (bind Delta' Gs') = (dom Delta').zip (GTy.tys Gs') := by rw [gsubst_ty_bind]; rfl
  have hv1 : Ty.substList (GSubst.ty (bind Delta' Gs')) (vars (dom Delta')) = GTy.tys Gs' := by
    rw [hsg]; exact vars_subst hN (by simp [gtys_length, hG', dom])
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
  have hmo' := MethodOk.ren hwf hok hd hmeth' hF.1 env hnM hnM' htM htM' huM huM'
  have hmi := methodOk_inv hmo'
  simp only [List.nil_append] at hmi
  have hbF : forall b, List.Mem b Delta' ->
      Sub d [] ((Ty.var b.X).subst (GSubst.ty (bind Delta' Gs'))) (b.T.subst (GSubst.ty (bind Delta' Gs'))) /\
      Kind d [] ((Ty.var b.X).subst (GSubst.ty (bind Delta' Gs'))) := by
    intro b hb
    have hss := hw.subs
    rw [<- hcod] at hss
    rcases bounds_sat_aux (by rw [gtys_length]; exact hG') hss hw.kinds b hb with ⟨U, hU⟩
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
  have hfst : (bind Delta' Gs').map Prod.fst = dom Delta' := bind_fst hG'
  have htv0 : Typing d [] [] v0.expr (.cls C (GTy.tys Gs)) := by
    have := vt.2.1
    rw [hv] at this |-
    simpa [typeOf] using this
  have hs2 := hsig
  simp only [Ty.substList, List.cons.injEq] at hs2
  have eg : (Ty.cls C (GTy.tys Gs)).subst (GSubst.ty (bind Delta' Gs')) = Ty.cls C (GTy.tys Gs) :=
    GTy.subst_ty (GTy.cls C Gs)
  have hres := found_tail hwf hok hd hmi.2.2 hgok hfst hN' hp hgs hvs hnx ht0 hu0 ha'
    (by simp only [Ty.substList]; rw [eg, hs2.2]; exact TypingSeq.cons htv0 hw.args) ha.2.2.2.2.1 (WFExpr.noThis ha)
    (WFExpr.uniq ha)
  rw [hs2.1] at hres
  exact hw.up.typing hres

end Funnelling
