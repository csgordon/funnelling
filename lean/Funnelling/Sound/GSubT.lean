import Funnelling.Sound.RenOver

open Funnelling.SoundSimp

namespace Funnelling.High

abbrev GOk (d : Decls) (Delta : Bounds) (s : GSubst) : Prop :=
  forall b, List.Mem b Delta -> forall G, List.lookup b.X s = some G ->
    Sub d [] G.ty (b.T.subst s.ty) /\ Kind d [] G.ty /\ Kind d [] (b.T.subst s.ty)

abbrev gsubB (s : GSubst) (Delta : Bounds) : Bounds :=
  Bounds.subst s.ty (Delta.filter fun b => !((s.map Prod.fst).contains b.X))

abbrev gsubG (s : GSubst) (gamma : Gamma) : Gamma := gamma.map (VarDecl.subst s.ty)

theorem GOk.substCtx {d : Decls} {Delta : Bounds} {s : GSubst} (h : GOk d Delta s) :
    SubstCtx d Delta (gsubB s Delta) s.ty := by
  intro b hb
  cases hl : List.lookup b.X s with
  | none =>
    refine Or.inl (Exists.intro b.X (And.intro ?_ ?_))
    . simp only [Ty.subst, GSubst.lookup_ty, hl, Option.map_none, Option.getD_none]
    . simp only [gsubB, Bounds.subst, listMem_iff, List.mem_map, List.mem_filter]
      refine Exists.intro b (And.intro (And.intro hb ?_) rfl)
      have := lookup_none_not_dom' hl
      simpa using this
  | some G =>
    have hg := h b hb G hl
    have e : (Ty.var b.X).subst s.ty = G.ty := by
      simp only [Ty.subst, GSubst.lookup_ty, hl, Option.map_some, Option.getD_some]
    rw [e]
    have hG := hg.2.1
    cases G with
    | cls C Gs =>
      refine Or.inr (And.intro (Sub.cls_indep hg.1) (And.intro (Kind.mono (fun _ h => by cases h) hg.2.1)
        (Kind.mono (fun _ h => by cases h) hg.2.2)))
where
  lookup_none_not_dom' {X : TVarName} {s : GSubst} (h : List.lookup X s = none) : Not (List.Mem X (s.map Prod.fst)) := by
    intro hm
    cases lookup_isSome hm with
    | intro v hv => rw [hv] at h; cases h

theorem GOk.append {d : Decls} {Delta Dm : Bounds} {s : GSubst} (h : GOk d Delta s)
    (hm : forall b, List.Mem b Dm -> Not (List.Mem b.X (s.map Prod.fst))) : GOk d (Delta ++ Dm) s := by
  intro b hb G hl
  simp only [listMem_iff, List.mem_append] at hb
  rcases hb with hb | hb
  . exact h b hb G hl
  . exact absurd (lookup_some_mem_dom hl) (hm b hb)

theorem GOk.mono {d : Decls} {Delta Delta2 : Bounds} {s : GSubst} (h : GOk d Delta s) (hs : Sub1 Delta2 Delta) :
    GOk d Delta2 s := fun b hb => h b (hs b hb)

theorem gsubB_append {s : GSubst} {Delta Dm : Bounds}
    (hm : forall b, List.Mem b Dm -> Not (List.Mem b.X (s.map Prod.fst))) :
    gsubB s (Delta ++ Dm) = gsubB s Delta ++ Bounds.subst s.ty Dm := by
  simp only [gsubB, List.filter_append, Bounds.subst, List.map_append]
  congr 2
  apply List.filter_eq_self.mpr
  intro b hb
  simpa using hm b hb

theorem Gamma.lookup_gsubG {s : GSubst} {x : VarName} {T : Ty} : forall {gamma : Gamma}, gamma.lookup x = some T ->
    (gsubG s gamma).lookup x = some (T.subst s.ty)
  | [], h => by simp [Gamma.lookup] at h
  | y :: gamma, h => by
    by_cases hy : y.x = x
    . simp only [Gamma.lookup, List.find?_cons, hy, beq_self_eq_true, Option.map_some] at h |-
      simp only [gsubG, List.map_cons, List.find?_cons, VarDecl.subst, hy, beq_self_eq_true, Option.map_some]
      cases h
      rfl
    . have hb : (y.x == x) = false := by simpa using hy
      simp only [Gamma.lookup, List.find?_cons, hb] at h |-
      simp only [gsubG, List.map_cons, List.find?_cons, VarDecl.subst, hb]
      exact Gamma.lookup_gsubG (gamma := gamma) h

theorem gdom_gsubG {s : GSubst} {gamma : Gamma} : gdom (gsubG s gamma) = gdom gamma := by
  simp [gdom, gsubG, VarDecl.subst, List.map_map, Function.comp_def]

theorem Expr.gsubstList_append {s : GSubst} : forall {es1 es2 : List Expr},
    Expr.gsubstList s (es1 ++ es2) = Expr.gsubstList s es1 ++ Expr.gsubstList s es2
  | [], _ => rfl
  | e :: es1, es2 => by simp only [List.cons_append, Expr.gsubstList]; rw [Expr.gsubstList_append]

theorem tbindersList_append : forall {es1 es2 : List Expr},
    Expr.tbindersList (es1 ++ es2) = Expr.tbindersList es1 ++ Expr.tbindersList es2
  | [], _ => rfl
  | e :: es1, es2 => by simp only [List.cons_append, Expr.tbindersList]; rw [tbindersList_append, List.append_assoc]

theorem tbindersListM_mem {M : Method} {X : TVarName} : forall {Ms : List Method}, List.Mem M Ms ->
    List.Mem X M.tbinders -> List.Mem X (Method.tbindersList Ms)
  | [], h, _ => by cases h
  | M' :: Ms, h, hx => by
    simp only [Method.tbindersList, listMem_iff, List.mem_append]
    cases h with
    | head => exact Or.inl hx
    | tail _ h => exact Or.inr (tbindersListM_mem h hx)

theorem substList_app {s : TSubst} {Ts Us : List Ty} :
    Ty.substList s (Ts ++ Us) = Ty.substList s Ts ++ Ty.substList s Us := by
  simp [substList_eq_map]

theorem cod_subst {s : TSubst} {Dm : Bounds} : cod (Bounds.subst s Dm) = Ty.substList s (cod Dm) := by
  simp [cod, Bounds.subst, substList_eq_map, List.map_map, Function.comp_def]

theorem params_T_subst {s : TSubst} {ps : List VarDecl} :
    (ps.map (VarDecl.subst s)).map VarDecl.T = Ty.substList s (ps.map VarDecl.T) := by
  simp [VarDecl.subst, substList_eq_map, List.map_map, Function.comp_def]

theorem KindSeq.substC {d : Decls} (hd : DeclOk d) {Delta Delta' : Bounds} {s : TSubst} (hc : SubstCtx d Delta Delta' s)
    {Ts : List Ty} (h : KindSeq d Delta Ts) : KindSeq d Delta' (Ty.substList s Ts) := by
  intro T hT
  rw [substList_eq_map] at hT
  cases List.mem_map.mp hT with
  | intro U hU => rw [<- hU.2]; exact Kind.subst hd hc.sub hc.kind (h U hU.1)

theorem Typing.gsub_newLocal {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {Delta : Bounds}
    {gamma : Gamma} {C : ClassName} {Fs : List Funnel} {C0 : ClassName} {Ts : List Ty} {es : List Expr}
    {Ms : List Method} {Delta' : Bounds} {Ts'' : List Ty} {T'' : Ty} {s : GSubst} {Xs : List TVarName}
    {xs : List VarName}
    (h1 : Consistent d (.loc C Fs C0 Ts es Ms)) (h2 : Pairing Delta Fs (abs Fs) Delta' Ts'')
    (h3 : forall X, List.Mem X (Ty.ftvList (cod Delta')) -> List.Mem X (dom Delta'))
    (h4 : Kind d Delta' (.cls C (abs Fs))) (h5 : Kind d Delta' (.cls C0 Ts))
    (h8 : OverrideOk d Delta' (.cls C0 Ts) Ms)
    (ih6 : Typing d (gsubB s Delta) (gsubG s gamma) ((Expr.new C0 Ts es).gsubst s) (T''.subst s.ty))
    (ih7 : forall M, List.Mem M Ms -> MethodOk d (gsubB s Delta') (gsubG s (innerG gamma Fs C)) (M.gsubst s))
    (hg : GOk d Delta s)
    (hdis : forall X, List.Mem X (Expr.newLocal C Fs C0 Ts es Ms).tbinders -> Not (List.Mem X (s.map Prod.fst)))
    (n1 : (gdom gamma).Nodup) (sc : Sub1 (gdom gamma) xs) (hn : (Expr.newLocal C Fs C0 Ts es Ms).noShadow Xs xs = true)
    (ht : NoThis (Expr.newLocal C Fs C0 Ts es Ms)) (hu : (Expr.newLocal C Fs C0 Ts es Ms).uniq) :
    Typing d (gsubB s Delta) (gsubG s gamma) ((Expr.newLocal C Fs C0 Ts es Ms).gsubst s)
      ((Ty.cls C (abs Fs)).subst s.ty) := by
  sorry

mutual
theorem Typing.gsub {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma e T}, Typing d Delta gamma e T ->
    forall {s Xs xs}, GOk d Delta s -> (forall X, List.Mem X e.tbinders -> Not (List.Mem X (s.map Prod.fst))) ->
    (gdom gamma).Nodup -> Sub1 (gdom gamma) xs -> e.noShadow Xs xs = true -> NoThis e -> e.uniq ->
    Typing d (gsubB s Delta) (gsubG s gamma) (e.gsubst s) (T.subst s.ty)
  | _, _, _, _, .subs h hk hs, _, _, _, hg, hdis, n1, sc, hn, ht, hu =>
    Typing.subs (Typing.gsub hwf hok hd h hg hdis n1 sc hn ht hu) (Kind.subst hd hg.substCtx.sub hg.substCtx.kind hk)
      (Sub.subst hd hg.substCtx.sub hs)
  | _, _, _, _, .var hl, _, _, _, _, _, _, _, _, _, _ => by
    simp only [Expr.gsubst]
    exact Typing.var (Gamma.lookup_gsubG hl)
  | _, _, _, _, .newObject, _, _, _, _, _, _, _, _, _, _ => by
    simp only [Expr.gsubst, Expr.gsubstList, Ty.substList, Ty.subst]
    exact Typing.newObject
  | _, _, _, _, .declField h1 h2 h3 h4, s, _, _, hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Expr.noShadow] at hn
    simp only [Expr.tbinders] at hdis
    simp only [NoThis, Expr.vbinders] at ht
    simp only [Expr.uniq] at hu
    have ih := Typing.gsub hwf hok hd h1 hg hdis n1 sc hn ht hu
    simp only [Ty.subst] at ih
    simp only [Expr.gsubst]
    rw [subst_bind_comp h4 (field_closed hok h2 h3)]
    exact Typing.declField ih h2 h3 (by rw [substList_length, h4])
  | _, _, _, _, .call (Delta0 := Delta0) (Delta1 := Delta1) (Ts2 := Ts2) (Ts1 := Ts1) h1 h2 h3 h4 h5 h6 h7 h8 h9, s, _, _,
      hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hdis
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq] at hu
    have hcl := methodIn_closed hwf hok h2 h3
    have ih1 := Typing.gsub hwf hok hd h1 hg (fun X hX => hdis X (Or.inl hX)) n1 sc hn.1 ht.1 hu.1
    simp only [Ty.subst] at ih1
    have ih2 := TypingSeq.gsub hwf hok hd h9 hg (fun X hX => hdis X (Or.inr hX)) n1 sc hn.2 ht.2 hu.2
    have hlen : (Ts2 ++ Ts1).length = (Delta0 ++ Delta1).length := by simp [h4, h5]
    have e6 := congrArg (Ty.substList s.ty) h6
    rw [substList_bind_comp hlen hcl.1, substList_app] at e6
    simp only [Ty.substList] at e6
    simp only [Expr.gsubst]
    refine Typing.call ih1 (by have := Scope.subst (s := s.ty) h2; simpa only [Ty.subst] using this) h3
      (by rw [substList_length, h4]) (by rw [substList_length, h5]) e6
      (KindSeq.substC hd hg.substCtx h7) ?_ ih2
    have := SubSeq.subst hd hg.substCtx.sub h8
    rwa [substList_bind_comp hlen hcl.2, substList_app] at this
  | _, _, _, _, .callLbRuntime (D0 := D0) (Ts0 := Ts0) (Delta1 := Delta1) (Ts1 := Ts1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11,
      s, _, _, hg, hdis, n1, sc, hn, ht, hu => by
    have hcl := methodIn_closed hwf hok (Scope.dec (Ts := Ts0) h2) h3
    have ih := TypingSeq.gsub hwf hok hd h11 hg
      (fun X hX => hdis X (by simpa [Expr.tbindersList, Expr.tbinders] using hX))
      n1 sc (by simpa [Expr.noShadowList, Expr.noShadow] using hn)
      (by simpa [NoThis, Expr.vbindersList, Expr.vbinders] using ht)
      (by simpa [Expr.uniqList, Expr.uniq] using hu)
    simp only [Expr.gsubstList, Ty.substList, Ty.subst] at ih
    have hlen : (Ts0 ++ Ts1).length = (D0.bounds ++ Delta1).length := by simp [h4, h5]
    have e6 := congrArg (Ty.substList s.ty) h6
    rw [substList_bind_comp hlen hcl.1, substList_app] at e6
    simp only [Ty.substList] at e6
    have hs1 := Sub.subst hd hg.substCtx.sub h1
    have hk8 := Kind.subst hd hg.substCtx.sub hg.substCtx.kind h8
    simp only [Ty.subst] at hs1 hk8
    simp only [Expr.gsubst, Ty.subst]
    refine Typing.callLbRuntime hs1 h2 h3 (by rw [substList_length, h4]) (by rw [substList_length, h5]) e6 h7 hk8
      (KindSeq.substC hd hg.substCtx h9) ?_ ih
    have := SubSeq.subst hd hg.substCtx.sub h10
    rwa [substList_bind_comp hlen hcl.2, substList_app] at this
  | _, _, _, _, .newTop (D := D) h1 h2 h3 h4 h5, s, _, _, hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Expr.noShadow, noShadowList_append, Bool.and_eq_true] at hn
    simp only [Expr.tbinders, tbindersList_append, listMem_iff, List.mem_append] at hdis
    simp only [NoThis, Expr.vbinders, vbindersList_append, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq, uniqList_append] at hu
    have ih1 := TypingSeq.gsub hwf hok hd h4 hg (fun X hX => hdis X (Or.inl hX)) n1 sc hn.1 ht.1 hu.1
    have ih2 := Typing.gsub hwf hok hd h5 hg (fun X hX => hdis X (Or.inr (by simpa [Expr.tbinders] using hX))) n1 sc
      (by simpa [Expr.noShadow] using hn.2) (by simpa [NoThis, Expr.vbinders] using ht.2)
      (by simpa [Expr.uniq] using hu.2)
    rw [substList_bind_comp h3 (slots_closed hok h1)] at ih1
    simp only [Expr.gsubst] at ih2
    rw [substList_bind_comp h3 (hd.supD D h1)] at ih2
    have hk2 := Kind.subst hd hg.substCtx.sub hg.substCtx.kind h2
    simp only [Ty.subst] at hk2
    simp only [Expr.gsubst, Expr.gsubstList_append, Ty.subst]
    exact Typing.newTop h1 hk2 (by rw [substList_length, h3]) ih1 ih2
  | _, gamma, _, _, .newLocal (C := C) (Fs := Fs) (Ms := Ms) (Delta' := Dp) h1 h2 h3 h4 h5 h6 h7 h8, s, Xs, xs,
      hg, hdis, n1, sc, hn, ht, hu => by
    have hn0 := hn
    have hdis0 := hdis
    have ht0 := ht
    have hu0 := hu
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hdis
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq] at hu
    have ih6 := Typing.gsub hwf hok hd h6 hg (fun X hX => hdis X (Or.inl (by simpa [Expr.tbinders] using hX))) n1 sc
      (by simpa [Expr.noShadow] using hn.1) (by simpa [NoThis, Expr.vbinders] using ht.1)
      (by simpa [Expr.uniq] using hu.1)
    refine Typing.gsub_newLocal hwf hok hd h1 h2 h3 h4 h5 h8 ih6 ?_ hg hdis0 n1 sc hn0 ht0 hu0
    intro M hM
    exact MethodOk.gsub hwf hok hd (h7 M hM) (hg.mono h2.sub)
      (fun X hX => hdis X (Or.inr (tbindersListM_mem hM hX))) (innerG_nodup n1 _ _) (innerG_dom sc _ _)
      (noShadowListM_all hn.2 hM) (fun h => ht.2 (vbindersListM_mem hM h)) (uniqList_mem hM hu.2)
  | Delta, gamma, _, _, .ifInstanceof (e0 := e0) (x := x) h0 hk hc h1 h2, s, _, xs, hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hdis
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht
    simp only [Expr.uniq] at hu
    have hxs : Not (List.Mem x xs) := by have := hn.1.1.2; simp at this; exact this
    have ih0 := Typing.gsub hwf hok hd h0 hg (fun X hX => hdis X (Or.inl (Or.inl hX))) n1 sc hn.1.1.1 ht.1.1.2 hu.1
    have ih1 := Typing.gsub hwf hok hd h1 (xs := x :: xs) hg (fun X hX => hdis X (Or.inl (Or.inr hX)))
      (by rw [gdom_append_single]; exact nodup_snoc n1 (fun h => hxs (sc _ h)))
      (by
        rw [gdom_append_single]
        intro z hz
        simp only [listMem_iff, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        . exact List.Mem.tail _ (sc z hz)
        . rw [hz]; exact List.Mem.head _)
      hn.1.2 ht.1.2 hu.2.1
    have ih2 := Typing.gsub hwf hok hd h2 hg (fun X hX => hdis X (Or.inr hX)) n1 sc hn.2 ht.2 hu.2.2
    simp only [gsubG, List.map_append, List.map_cons, List.map_nil, VarDecl.subst] at ih1
    simp only [Expr.gsubst]
    cases Cast.gsub hd hg.substCtx hc with
    | intro T1 hT1 =>
      have ty0 : Typing d (gsubB s Delta) (gsubG s gamma) (Expr.gsubst s e0) T1 := by
        rcases hT1.2.2 with e | hk1
        . rw [e]; exact ih0
        . exact Typing.subs ih0 hk1 hT1.1
      exact Typing.ifInstanceof ty0 (Kind.subst hd hg.substCtx.sub hg.substCtx.kind hk) hT1.2.1 ih1 ih2
theorem TypingSeq.gsub {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma es Ts}, TypingSeq d Delta gamma es Ts ->
    forall {s Xs xs}, GOk d Delta s ->
    (forall X, List.Mem X (Expr.tbindersList es) -> Not (List.Mem X (s.map Prod.fst))) ->
    (gdom gamma).Nodup -> Sub1 (gdom gamma) xs -> Expr.noShadowList Xs xs es = true ->
    Not (List.Mem this (Expr.vbindersList es)) -> Expr.uniqList es ->
    TypingSeq d (gsubB s Delta) (gsubG s gamma) (Expr.gsubstList s es) (Ty.substList s.ty Ts)
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, _ => TypingSeq.nil
  | _, _, _, _, .cons h hs, _, _, _, hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at hn
    simp only [Expr.tbindersList, listMem_iff, List.mem_append] at hdis
    simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniqList] at hu
    simp only [Expr.gsubstList, Ty.substList]
    exact TypingSeq.cons (Typing.gsub hwf hok hd h hg (fun X hX => hdis X (Or.inl hX)) n1 sc hn.1 ht.1 hu.1)
      (TypingSeq.gsub hwf hok hd hs hg (fun X hX => hdis X (Or.inr hX)) n1 sc hn.2 ht.2 hu.2)
theorem MethodOk.gsub {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma M}, MethodOk d Delta gamma M ->
    forall {s Xs xs}, GOk d Delta s -> (forall X, List.Mem X M.tbinders -> Not (List.Mem X (s.map Prod.fst))) ->
    (gdom gamma).Nodup -> Sub1 (gdom gamma) (this :: xs) -> M.noShadow Xs xs = true -> NoThisM M -> M.uniq ->
    MethodOk d (gsubB s Delta) (gsubG s gamma) (M.gsubst s)
  | _, gamma, _, .methodOk (Delta' := Dm) (ps := ps) h1 h2 h3, s, Xs, xs, hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Method.noShadow, Bool.and_eq_true] at hn
    simp only [Method.tbinders, listMem_iff, List.mem_append] at hdis
    simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Method.uniq] at hu
    have hdm : forall b, List.Mem b Dm -> Not (List.Mem b.X (s.map Prod.fst)) :=
      fun b hb => hdis b.X (Or.inl (List.mem_map_of_mem (f := Bound.X) hb))
    have hpx : forall p, List.Mem p (ps.map VarDecl.x) -> Not (List.Mem p xs) :=
      fun p hp => not_mem_of_all_not_contains hn.1.2 hp
    have hnod : (gdom (gamma ++ ps)).Nodup := by
      simp only [gdom, List.map_append]
      apply List.nodup_append.mpr
      refine And.intro n1 (And.intro hu.2.1 ?_)
      intro a ha b hb' e
      subst e
      have := sc a ha
      cases this with
      | head => exact ht.1 hb'
      | tail _ h => exact hpx a hb' h
    have hg2 := hg.append hdm
    have hc2 := hg2.substCtx
    rw [gsubB_append hdm] at hc2
    have hb := Typing.gsub hwf hok hd h3 (xs := this :: xs ++ ps.map VarDecl.x) hg2 (fun X hX => hdis X (Or.inr hX))
      hnod
      (by
        intro z hz
        simp only [gdom, List.map_append, listMem_iff, List.mem_append] at hz
        simp only [listMem_iff, List.mem_append, List.mem_cons]
        rcases hz with hz | hz
        . have := sc z hz
          cases this with
          | head => exact Or.inl (Or.inl rfl)
          | tail _ h => exact Or.inl (Or.inr h)
        . exact Or.inr hz)
      hn.2 ht.2 hu.2.2
    rw [gsubB_append hdm] at hb
    simp only [gsubG, List.map_append] at hb
    simp only [Method.gsubst]
    refine MethodOk.methodOk ?_ ?_ hb
    . rw [cod_subst]; exact KindSeq.substC hd hc2 h1
    . have := KindSeq.substC hd hc2 h2
      simp only [Ty.substList] at this
      rw [params_T_subst]
      exact this
end

end Funnelling.High
