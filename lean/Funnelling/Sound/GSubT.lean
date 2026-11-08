import Funnelling.Sound.GSubLoc

open Funnelling.SoundSimp

namespace Funnelling.High

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
    exact Typing.var (Gamma.lookup_gsubG hl)
  | _, _, _, _, .newObject, _, _, _, _, _, _, _, _, _, _ => by
    exact Typing.newObject
  | _, _, _, _, .declField h1 h2 h3 h4, s, _, _, hg, hdis, n1, sc, hn, ht, hu => by
    have ih := Typing.gsub hwf hok hd h1 hg hdis n1 sc hn ht hu
    rw [subst_bind_comp h4 (field_closed hok h2 h3)]
    exact Typing.declField ih h2 h3 (by rw [substList_length, h4])
  | _, _, _, _, .call (Delta0 := Delta0) (Delta1 := Delta1) (Ts2 := Ts2) (Ts1 := Ts1) h1 h2 h3 h4 h5 h6 h7 h8 h9, s, _, _,
      hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.tbinders, listMem_iff, List.mem_append, NoThis, Expr.vbinders,
      not_or, Expr.uniq] at hn hdis ht hu
    have hcl := methodIn_closed hwf hok h2 h3
    have ih1 := Typing.gsub hwf hok hd h1 hg (fun X hX => hdis X (Or.inl hX)) n1 sc hn.1 ht.1 hu.1
    have ih2 := TypingSeq.gsub hwf hok hd h9 hg (fun X hX => hdis X (Or.inr hX)) n1 sc hn.2 ht.2 hu.2
    have hlen : (Ts2 ++ Ts1).length = (Delta0 ++ Delta1).length := by simp [h4, h5]
    have e6 := congrArg (Ty.substList s.ty) h6
    rw [substList_bind_comp hlen hcl.1, substList_app] at e6
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
    have hlen : (Ts0 ++ Ts1).length = (D0.bounds ++ Delta1).length := by simp [h4, h5]
    have e6 := congrArg (Ty.substList s.ty) h6
    rw [substList_bind_comp hlen hcl.1, substList_app] at e6
    have hs1 := Sub.subst hd hg.substCtx.sub h1
    have hk8 := Kind.subst hd hg.substCtx.sub hg.substCtx.kind h8
    refine Typing.callLbRuntime hs1 h2 h3 (by rw [substList_length, h4]) (by rw [substList_length, h5]) e6 h7 hk8
      (KindSeq.substC hd hg.substCtx h9) ?_ ih
    have := SubSeq.subst hd hg.substCtx.sub h10
    rwa [substList_bind_comp hlen hcl.2, substList_app] at this
  | _, _, _, _, .newTop (D := D) h1 h2 h3 h4 h5, s, _, _, hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Expr.noShadow, noShadowList_append, Bool.and_eq_true, Expr.tbinders, tbindersList_append, listMem_iff,
      List.mem_append, NoThis, Expr.vbinders, vbindersList_append, not_or, Expr.uniq,
      uniqList_append] at hn hdis ht hu
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
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.tbinders, listMem_iff, List.mem_append, NoThis, Expr.vbinders,
      not_or, Expr.uniq] at hn hdis ht hu
    have ih6 := Typing.gsub hwf hok hd h6 hg (fun X hX => hdis X (Or.inl (by simpa [Expr.tbinders] using hX))) n1 sc
      (by simpa [Expr.noShadow] using hn.1) (by simpa [NoThis, Expr.vbinders] using ht.1)
      (by simpa [Expr.uniq] using hu.1)
    refine Typing.gsub_newLocal hwf hok hd h1 h2 h3 h4 h5 h8 ih6 ?_ hg hdis0 n1 sc hn0 ht0 hu0
    intro M hM
    exact MethodOk.gsub hwf hok hd (h7 M hM) (hg.mono h2.sub)
      (fun X hX => hdis X (Or.inr (tbindersListM_mem hM hX))) (innerG_nodup n1 _ _) (innerG_dom sc _ _)
      (noShadowListM_mem hM hn.2) (fun h => ht.2 (vbindersListM_mem hM h)) (uniqList_mem hM hu.2)
  | Delta, gamma, _, _, .ifInstanceof (e0 := e0) (x := x) h0 hk hc h1 h2, s, _, xs, hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true', Expr.tbinders, listMem_iff, List.mem_append,
      NoThis, Expr.vbinders, List.mem_cons, not_or, Expr.uniq] at hn hdis ht hu
    have hxs : Not (List.Mem x xs) := by have := hn.1.1.2; simp at this; exact this
    have ih0 := Typing.gsub hwf hok hd h0 hg (fun X hX => hdis X (Or.inl (Or.inl hX))) n1 sc hn.1.1.1 ht.1.1.2 hu.1
    have ih1 := Typing.gsub hwf hok hd h1 (xs := x :: xs) hg (fun X hX => hdis X (Or.inl (Or.inr hX)))
      (by rw [gdom_append_single]; exact nodup_snoc n1 (fun h => hxs (sc _ h)))
      (scope_snoc sc)
      hn.1.2 ht.1.2 hu.2.1
    have ih2 := Typing.gsub hwf hok hd h2 hg (fun X hX => hdis X (Or.inr hX)) n1 sc hn.2 ht.2 hu.2.2
    simp only [gsubG, List.map_append, List.map_cons, List.map_nil, VarDecl.subst] at ih1
    simp only [Expr.gsubst]
    rcases Cast.gsub hd hg.substCtx hc with ⟨T1, hT1⟩
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
    simp only [Expr.noShadowList, Bool.and_eq_true, Expr.tbindersList, listMem_iff, List.mem_append,
      Expr.vbindersList, not_or, Expr.uniqList] at hn hdis ht hu
    simp only [Expr.gsubstList, Ty.substList]
    exact TypingSeq.cons (Typing.gsub hwf hok hd h hg (fun X hX => hdis X (Or.inl hX)) n1 sc hn.1 ht.1 hu.1)
      (TypingSeq.gsub hwf hok hd hs hg (fun X hX => hdis X (Or.inr hX)) n1 sc hn.2 ht.2 hu.2)
theorem MethodOk.gsub {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma M}, MethodOk d Delta gamma M ->
    forall {s Xs xs}, GOk d Delta s -> (forall X, List.Mem X M.tbinders -> Not (List.Mem X (s.map Prod.fst))) ->
    (gdom gamma).Nodup -> Sub1 (gdom gamma) (this :: xs) -> M.noShadow Xs xs = true -> NoThisM M -> M.uniq ->
    MethodOk d (gsubB s Delta) (gsubG s gamma) (M.gsubst s)
  | _, gamma, _, .methodOk (Delta' := Dm) (ps := ps) h1 h2 h3, s, Xs, xs, hg, hdis, n1, sc, hn, ht, hu => by
    simp only [Method.noShadow, Bool.and_eq_true, Method.tbinders, listMem_iff, List.mem_append, NoThisM,
      Method.vbinders, not_or, Method.uniq] at hn hdis ht hu
    have hdm : forall b, List.Mem b Dm -> Not (List.Mem b.X (s.map Prod.fst)) :=
      fun b hb => hdis b.X (Or.inl (List.mem_map_of_mem (f := Bound.X) hb))
    have hg2 := hg.append hdm
    have hc2 := hg2.substCtx
    rw [gsubB_append hdm] at hc2
    have hb := Typing.gsub hwf hok hd h3 (xs := this :: xs ++ ps.map VarDecl.x) hg2 (fun X hX => hdis X (Or.inr hX))
      (nodup_params n1 sc hu.2.1 ht.1 hn.1.2) (scope_params sc) hn.2 ht.2 hu.2.2
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
