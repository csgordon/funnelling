import Funnelling.Sound.Preservation

open Funnelling.SoundSimp

namespace Funnelling

mutual
theorem Ty.ground_of : forall {T : Ty}, T.ftv = [] -> exists G : GTy, T = G.ty
  | .var _, h => by simp [Ty.ftv] at h
  | .cls C Ts, h => by
    rcases Ty.groundList_of h with ⟨Gs, hG⟩; exact Exists.intro (.cls C Gs) (by rw [hG]; rfl)
theorem Ty.groundList_of : forall {Ts : List Ty}, Ty.ftvList Ts = [] -> exists Gs : List GTy, Ts = GTy.tys Gs
  | [], _ => Exists.intro [] rfl
  | T :: Ts, h => by
    simp only [Ty.ftvList, List.append_eq_nil_iff] at h
    rcases Ty.ground_of h.1 with ⟨G, hG⟩
    rcases Ty.groundList_of h.2 with ⟨Gs, hGs⟩; exact Exists.intro (G :: Gs) (by rw [hG, hGs]; rfl)
end

theorem all_nil_contains {A : Type} [DecidableEq A] : forall {l : List A}, l.all ([] : List A).contains = true -> l = []
  | [], _ => rfl
  | _ :: _, h => by simp at h

theorem funnels_ground : forall {Fs : List Funnel}, domF Fs = [] -> exists Gs : List GTy, Fs = Gs.map Funnel.ground
  | [], _ => Exists.intro [] rfl
  | .funnel _ :: _, h => by simp [domF] at h
  | .ground G :: Fs, h => by
    have h' : domF Fs = [] := by simpa [domF] using h
    rcases funnels_ground h' with ⟨Gs, hGs⟩; exact Exists.intro (G :: Gs) (by rw [hGs]; rfl)

inductive Redex : Expr -> Prop
  | field (v : Value) (f : FieldName) : Redex (.field v.expr f)
  | call (v : Value) (Gs : List GTy) (m : MethName) (vs : List Value) :
      Redex (.call v.expr (GTy.tys Gs) m (Value.exprs vs))
  | super (v : Value) (G : GTy) (Gs : List GTy) (m : MethName) (vs : List Value) :
      Redex (.superCall v.expr G.ty (GTy.tys Gs) m (Value.exprs vs))
  | ifInst (v : Value) (G : GTy) (x : VarName) (e1 e2 : Expr) : Redex (.ifInst v.expr G.ty x e1 e2)

mutual
theorem decomp_closed : forall {e : Expr}, e.closed [] [] = true ->
    IsValue e \/ exists (E : ECtx) (r : Expr), e = E.plug r /\ Redex r
  | .var _, h => by simp [Expr.closed] at h
  | .call e Ts m es, h => by
    simp only [Expr.closed, Bool.and_eq_true] at h
    rcases Ty.groundList_of (all_nil_contains h.1.2) with ⟨Gs, hGs⟩
    subst hGs
    right
    rcases decomp_closed h.1.1 with ⟨v, hv⟩ | ⟨E, r, hE, hr⟩
    . subst hv
      rcases decomp_closedList h.2 with ⟨vs, hvs⟩ | ⟨vs, E, r, es', hE, hr⟩
      . subst hvs; exact ⟨.hole, _, rfl, Redex.call v Gs m vs⟩
      . subst hE; exact ⟨.callArg v Gs m vs E es', r, rfl, hr⟩
    . subst hE; exact ⟨.callRecv E Gs m es, r, rfl, hr⟩
  | .superCall e T Ts m es, h => by
    simp only [Expr.closed, Bool.and_eq_true, Ty.ftvList] at h
    have h0 := all_nil_contains h.1.2
    rw [List.append_eq_nil_iff] at h0
    rcases Ty.ground_of h0.1 with ⟨G, hG⟩
    rcases Ty.groundList_of h0.2 with ⟨Gs, hGs⟩
    subst hG hGs
    right
    rcases decomp_closed h.1.1 with ⟨v, hv⟩ | ⟨E, r, hE, hr⟩
    . subst hv
      rcases decomp_closedList h.2 with ⟨vs, hvs⟩ | ⟨vs, E, r, es', hE, hr⟩
      . subst hvs; exact ⟨.hole, _, rfl, Redex.super v G Gs m vs⟩
      . subst hE; exact ⟨.superArg v G Gs m vs E es', r, rfl, hr⟩
    . subst hE; exact ⟨.superRecv E G Gs m es, r, rfl, hr⟩
  | .field e f, h => by
    simp only [Expr.closed] at h
    right
    rcases decomp_closed h with ⟨v, hv⟩ | ⟨E, r, hE, hr⟩
    . subst hv; exact ⟨.hole, _, rfl, Redex.field v f⟩
    . subst hE; exact ⟨.field E f, r, rfl, hr⟩
  | .new C Ts es, h => by
    simp only [Expr.closed, Bool.and_eq_true] at h
    rcases Ty.groundList_of (all_nil_contains h.1) with ⟨Gs, hGs⟩
    subst hGs
    rcases decomp_closedList h.2 with ⟨vs, hvs⟩ | ⟨vs, E, r, es', hE, hr⟩
    . subst hvs; exact Or.inl ⟨Value.new C Gs vs, rfl⟩
    . subst hE; exact Or.inr ⟨.newArg C Gs vs E es', r, rfl, hr⟩
  | .newLocal C Fs C' Ts es Ms, h => by
    simp only [Expr.closed, Bool.and_eq_true] at h
    have h0 := all_nil_contains h.1.1
    rw [List.append_eq_nil_iff] at h0
    rcases funnels_ground h0.1 with ⟨Gs, hGs⟩
    rcases Ty.groundList_of h0.2 with ⟨Gs', hGs'⟩
    subst hGs hGs'
    rcases decomp_closedList h.1.2 with ⟨vs, hvs⟩ | ⟨vs, E, r, es', hE, hr⟩
    . subst hvs; exact Or.inl ⟨Value.newLocal C Gs C' Gs' vs Ms, rfl⟩
    . subst hE; exact Or.inr ⟨.localArg C Gs C' Gs' vs E es' Ms, r, rfl, hr⟩
  | .ifInst e0 T x e1 e2, h => by
    simp only [Expr.closed, Bool.and_eq_true] at h
    rcases Ty.ground_of (all_nil_contains h.1.1.2) with ⟨G, hG⟩
    subst hG
    right
    rcases decomp_closed h.1.1.1 with ⟨v, hv⟩ | ⟨E, r, hE, hr⟩
    . subst hv; exact ⟨.hole, _, rfl, Redex.ifInst v G x e1 e2⟩
    . subst hE; exact ⟨.ifCond E G x e1 e2, r, rfl, hr⟩
theorem decomp_closedList : forall {es : List Expr}, Expr.closedList [] [] es = true ->
    (exists vs : List Value, es = Value.exprs vs) \/
    exists (vs : List Value) (E : ECtx) (r : Expr) (es' : List Expr), es = Value.exprs vs ++ E.plug r :: es' /\ Redex r
  | [], _ => Or.inl ⟨[], rfl⟩
  | e :: es, h => by
    simp only [Expr.closedList, Bool.and_eq_true] at h
    rcases decomp_closed h.1 with ⟨v, hv⟩ | ⟨E, r, hE, hr⟩
    . subst hv
      rcases decomp_closedList h.2 with ⟨vs, hvs⟩ | ⟨vs, E, r, es', hE, hr⟩
      . subst hvs; exact Or.inl ⟨v :: vs, rfl⟩
      . subst hE; exact Or.inr ⟨v :: vs, E, r, es', rfl, hr⟩
    . subst hE; exact Or.inr ⟨[], E, r, es, rfl, hr⟩
end

mutual
theorem Expr.noShadow_tb : forall {e : Expr} {Xs : List TVarName} {xs : List VarName},
    e.noShadow Xs xs = true -> forall X, List.Mem X e.tbinders -> Not (List.Mem X Xs)
  | .var _, _, _, _, X, hX => by cases hX
  | .call e _ _ es, _, _, hn, X, hX => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.tbinders, listMem_iff, List.mem_append] at hn hX
    rcases hX with hX | hX
    . exact Expr.noShadow_tb hn.1 X hX
    . exact Expr.noShadowList_tb hn.2 X hX
  | .superCall e _ _ _ es, _, _, hn, X, hX => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.tbinders, listMem_iff, List.mem_append] at hn hX
    rcases hX with hX | hX
    . exact Expr.noShadow_tb hn.1 X hX
    . exact Expr.noShadowList_tb hn.2 X hX
  | .field e _, _, _, hn, X, hX => by
    simp only [Expr.noShadow, Expr.tbinders] at hn hX
    exact Expr.noShadow_tb hn X hX
  | .new _ _ es, _, _, hn, X, hX => Expr.noShadowList_tb hn X hX
  | .newLocal _ _ _ _ es Ms, _, _, hn, X, hX => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.tbinders, listMem_iff, List.mem_append] at hn hX
    rcases hX with hX | hX
    . exact Expr.noShadowList_tb hn.1 X hX
    . exact Method.noShadowList_tb hn.2 X hX
  | .ifInst e0 _ _ e1 e2, _, _, hn, X, hX => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.tbinders, listMem_iff, List.mem_append] at hn hX
    rcases hX with (hX | hX) | hX
    . exact Expr.noShadow_tb hn.1.1.1 X hX
    . exact Expr.noShadow_tb hn.1.2 X hX
    . exact Expr.noShadow_tb hn.2 X hX
theorem Expr.noShadowList_tb : forall {es : List Expr} {Xs : List TVarName} {xs : List VarName},
    Expr.noShadowList Xs xs es = true -> forall X, List.Mem X (Expr.tbindersList es) -> Not (List.Mem X Xs)
  | [], _, _, _, X, hX => by cases hX
  | e :: es, _, _, hn, X, hX => by
    simp only [Expr.noShadowList, Bool.and_eq_true, Expr.tbindersList, listMem_iff, List.mem_append] at hn hX
    rcases hX with hX | hX
    . exact Expr.noShadow_tb hn.1 X hX
    . exact Expr.noShadowList_tb hn.2 X hX
theorem Method.noShadow_tb : forall {M : Method} {Xs : List TVarName} {xs : List VarName},
    M.noShadow Xs xs = true -> forall X, List.Mem X M.tbinders -> Not (List.Mem X Xs)
  | .mk Delta _ _ ps e, _, _, hn, X, hX => by
    simp only [Method.noShadow, Bool.and_eq_true, Method.tbinders, listMem_iff, List.mem_append] at hn hX
    rcases hX with hX | hX
    . exact not_mem_of_all_not_contains hn.1.1 hX
    . intro hm
      exact Expr.noShadow_tb hn.2 X hX (List.mem_append_left _ hm)
theorem Method.noShadowList_tb : forall {Ms : List Method} {Xs : List TVarName} {xs : List VarName},
    Method.noShadowList Xs xs Ms = true -> forall X, List.Mem X (Method.tbindersList Ms) -> Not (List.Mem X Xs)
  | [], _, _, _, X, hX => by cases hX
  | M :: Ms, _, _, hn, X, hX => by
    simp only [Method.noShadowList, Bool.and_eq_true, Method.tbindersList, listMem_iff, List.mem_append] at hn hX
    rcases hX with hX | hX
    . exact Method.noShadow_tb hn.1 X hX
    . exact Method.noShadowList_tb hn.2 X hX
end

theorem idRen_nil {A : Type} : IdRen ([] : List (Prod A A)) := by intro p hp; cases hp

theorem FreshM.refl (M : Method) : FreshM M M :=
  And.intro (RenM.refl idRen_nil idRen_nil M) (RenM.refl idRen_nil idRen_nil M)

theorem inner_lens {d : Decls} (hwf : WFDecls d) {C C' : ClassName} {Gs Gs'' Gs' : List GTy}
    {vs0 vs : List Value} {Ms : List Method} {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl}
    {e0 : Expr} {T : Ty} (hM : List.Mem (Method.mk Delta' T0 m ps e0) Ms)
    (h : Typing d [] [] (.call (Value.newLocal C Gs C' Gs'' vs0 Ms).expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Gs'.length = Delta'.length /\ ps.length = vs.length := by
  rcases inv_call h rfl with ⟨⟨C0, Ts0, Delta0, Ts2, Delta1, T0c, psc, body, T0', Ts'⟩, hw⟩
  have vt := value_typing hwf hw.ty0
  have hsv := vt.1.sub
  have hty0 := vt.2.1
  rcases inv_local hty0 rfl with ⟨w2, hw2⟩
  have hD2 := pairing_ground_nil hw2.pair
  have hover := hw2.over
  rw [hD2] at hover
  rcases consistent_unfold hw2.cons with ⟨Fs', Ts'd, es', Ms'd, hcd, _, hcts, _, hcov⟩
  have hO : OverrideOkM d (.cls C0 Ts0) (Method.mk Delta' T0 m ps e0) := by
    rcases Sub.loc_step hwf hcd hsv with e | e
    . simp only [Ty.cls.injEq] at e
      rcases e with ⟨e1, e2⟩
      subst e1 e2
      have := hcov _ hM
      rwa [abs_ground] at this
    . have hs2 := e.2
      simp only [Ty.subst] at hs2
      rw [abs_ground] at hcts
      rw [<- hcts] at hs2
      exact hover _ C0 Ts0 hM hs2
  rcases found_sig hwf hw.scope hw.meth hw.len2 hO with ⟨_, h4, _, h6⟩
  have hl6 := congrArg List.length h6
  have hls := congrArg List.length hw.sig
  have hla : vs.length = Ts'.length := by
    have := TypingSeq.length hw.args
    rw [Value.exprs_eq_map, List.length_map] at this
    exact this
  simp only [substList_length, List.length_cons, List.length_map] at hl6 hls
  have hl1 := hw.len1
  rw [gtys_length] at hl1
  constructor <;> omega

theorem redex_step {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {r : Expr} {T : Ty}
    (hr : Redex r) (hw : WFExpr r) (ht : Typing d [] [] r T) : exists r', Step d r r' := by
  cases hr with
  | field v f =>
    rcases inv_field ht rfl with ⟨w, hw'⟩
    have vt := value_typing hwf hw'.ty
    have hsv := vt.1.sub
    cases v with
    | newLocal C Gs C' Gs' vs Ms => exact ⟨_, Step.innerFieldSuper⟩
    | new C Gs vs =>
      have hO : Not (C = Object) := by
        intro hO
        rw [hO] at hsv
        rcases sub_from_object hwf hsv with ⟨U, hU⟩
        simp only [Ty.cls.injEq] at hU
        have hm := hw'.mem
        rw [(Declared.object hwf hw'.decl hU.1).2.2.2.2] at hm
        cases hm
      have ht2 := vt.2.1
      rcases inv_new ht2 rfl with h1 | ⟨w2, hw2⟩
      . exact absurd h1.1 hO
      . have hn := hw2.name
        subst hn
        have hlen := hw2.len
        rw [gtys_length] at hlen
        have hl1 := TypingSeq.length hw2.fields
        rw [substList_length, List.length_map] at hl1
        have hsp := congrArg List.length hw2.split
        rw [List.length_append, Value.exprs_eq_map, List.length_map] at hsp
        have hk : (vs.take w2.D.Ss.length).length = w2.D.Ss.length := by rw [List.length_take]; omega
        rw [<- List.take_append_drop w2.D.Ss.length vs]
        by_cases hf : List.Mem f (w2.D.Ss.map Slot.f)
        . rcases mem_zip_fst (ys := vs.take w2.D.Ss.length) (by rw [List.length_map, hk]) hf with ⟨v, hv⟩
          exact ⟨_, Step.simpleFieldFound hw2.decl hk hv⟩
        . exact ⟨_, Step.simpleFieldSuper hw2.decl hk hf hO hlen⟩
  | call v Gs' m vs =>
    cases v with
    | new C Gs vs0 => exact ⟨_, Step.simpleAddSuper (v := Value.new C Gs vs0) rfl⟩
    | newLocal C Gs C' Gs'' vs0 Ms =>
      by_cases hm : List.Mem m (Ms.map Method.name)
      . rcases List.mem_map.mp hm with ⟨M, hM, hMn⟩
        cases M with
        | mk Delta' T0 m' ps e0 =>
        subst hMn
        have hl := inner_lens hwf hM ht
        have han := hw.2.2.2.2.1
        simp only [Expr.noShadow, Bool.and_eq_true] at han
        have hat := WFExpr.noThis hw
        simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at hat
        have hau := WFExpr.uniq hw
        have hv0n := han.1
        have hv0t := hat.1
        have hv0u := hau.1
        simp only [Value.expr, Expr.noShadow, Bool.and_eq_true, Expr.vbinders, List.mem_append, not_or,
          Expr.uniq] at hv0n hv0t hv0u
        have hnM : (Method.mk Delta' T0 m' ps e0).noShadow [] [] = true := by
          have := noShadowListM_mem hM hv0n.2
          simpa using this
        have htM : NoThisM (Method.mk Delta' T0 m' ps e0) := fun h => hv0t.2 (vbindersListM_mem hM h)
        have huM : (Method.mk Delta' T0 m' ps e0).uniq := uniqList_mem hM hv0u.2
        simp only [Method.noShadow, Bool.and_eq_true, List.nil_append, List.cons_append, NoThisM, Method.vbinders,
          listMem_iff, List.mem_append, not_or, Method.uniq] at hnM htM huM
        exact ⟨_, Step.innerFound (v0 := Value.newLocal C Gs C' Gs'' vs0 Ms) rfl hM (FreshM.refl _) hl.1 hl.2
          huM.1 (List.nodup_cons.mpr ⟨htM.1, huM.2.1⟩) (fun X hX => Expr.noShadow_tb hnM.2 X hX)
          (fun y hy => Expr.noShadow_binders hnM.2 htM.2 y hy) rfl⟩
      . exact ⟨_, Step.innerSuper rfl hm⟩
  | super v G Gs' m vs =>
    rcases inv_super ht rfl with ⟨w, hw'⟩
    have hann := hw'.ann
    cases G with
    | cls C Hs =>
      have hG : (GTy.cls C Hs).ty = Ty.cls C (GTy.tys Hs) := rfl
      rw [hG] at hann |-
      simp only [Ty.cls.injEq] at hann
      rcases hann with ⟨hC, hHs⟩
      subst hC
      have hkd0 := (kind_dec_args hwf hw'.decl hw'.kind).1
      have hkd := hkd0
      rw [<- hHs, gtys_length] at hkd
      by_cases hm : List.Mem m (w.D.Ms.map Method.name)
      . rcases List.mem_map.mp hm with ⟨M, hM, hMn⟩
        cases M with
        | mk Delta' T0 m' ps e0 =>
        subst hMn
        have hd := declOk hwf hok
        rcases dec_override hwf hok hd hw'.decl hM hw'.decl0 hkd0 hw'.sub with ⟨Us, hUs, hO, _⟩
        have hl2 : Us.length = w.D0.bounds.length := by rw [<- hw'.len0, hUs, substList_length]
        rcases found_sig hwf (Scope.dec hw'.decl0) hw'.meth hl2 hO with ⟨_, h4, _, h6⟩
        have hl6 := congrArg List.length h6
        have hls := congrArg List.length hw'.sig
        have hla := TypingSeq.length hw'.args
        simp only [substList_length, List.length_cons, List.length_map] at hl6 hls hla
        rw [Value.exprs_eq_map, List.length_map] at hla
        have hl1 := hw'.len1
        rw [gtys_length] at hl1
        rcases WFDecls.method hwf hw'.decl.dec_mem hM with ⟨huM, htM, hnM⟩
        have hnD : (dom w.D.bounds).Nodup := hwf.2.2.2.2.1 w.D.bounds (by
          simp only [listMem_iff, List.mem_append, List.mem_map]
          exact Or.inl (Exists.intro w.D (And.intro hw'.decl.dec_mem rfl)))
        have hdis := Method.noShadow_dom hnM
        simp only [Method.noShadow, Bool.and_eq_true, List.nil_append, List.cons_append, NoThisM, Method.vbinders,
          listMem_iff, List.mem_append, not_or, Method.uniq] at hnM htM huM
        have hN : (dom w.D.bounds ++ dom Delta').Nodup := by grind
        exact ⟨_, Step.simpleFound hw'.decl hM (FreshM.refl _) hkd (by omega) hN
          (List.nodup_cons.mpr ⟨htM.1, huM.2.1⟩) (by omega) (fun X hX => Expr.noShadow_tb hnM.2 X hX)
          (fun y hy => Expr.noShadow_binders hnM.2 htM.2 y hy) rfl⟩
      . have hO : Not (w.D.C = Object) := by
          intro hO
          have hs := hw'.sub
          rw [hO] at hs
          rcases sub_from_object hwf hs with ⟨U, hU⟩
          simp only [Ty.cls.injEq] at hU
          have hM := MethodIn.dec hwf hw'.decl0 hw'.meth
          rw [(Declared.object hwf hw'.decl0 hU.1).2.2.2.1] at hM
          cases hM
        exact ⟨_, Step.searchSuper hw'.decl hm hO hkd⟩
  | ifInst v G x e1 e2 =>
    cases G with
    | cls C' Hs =>
      have hG : (GTy.cls C' Hs).ty = Ty.cls C' (GTy.tys Hs) := rfl
      rw [hG]
      by_cases hs : exists Ts', Sub d [] (typeOf v) (.cls C' Ts')
      . rcases hs with ⟨Ts', hs⟩
        have hn := hw.2.2.2.2.1
        simp only [Expr.noShadow, Bool.and_eq_true] at hn
        have hth := WFExpr.noThis hw
        simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at hth
        exact ⟨_, Step.ifThen hs (Fresh.refl e1) (fun y hy => Expr.noShadow_binders hn.1.2 hth.1.2 y hy)⟩
      . exact ⟨_, Step.ifElse hs⟩

theorem progress_step {d : Decls} {e : Expr} {T : Ty} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (ht : Typing d [] [] e T) : IsValue e \/ exists e', Step d e e' := by
  rcases decomp_closed he.2.2.2.2.2.2 with hv | ⟨E, r, hE, hr⟩
  . exact Or.inl hv
  . subst hE
    rcases typing_plug E ht with ⟨Ta, hTa, _⟩
    rcases redex_step hwf hok hr (WFExpr.plug he) hTa with ⟨r', hr'⟩
    exact Or.inr ⟨_, Step.ctx hr'⟩

end Funnelling
