import Funnelling.Sound.GammaL

open Funnelling.SoundSimp

namespace Funnelling.High

theorem Pairing.mono {Delta Delta2 : Bounds} (hs : Sub1 Delta Delta2) {Fs : List Funnel} {Ts : List Ty}
    {D0 : Bounds} {T0 : List Ty} (h : Pairing Delta Fs Ts D0 T0) : Pairing Delta2 Fs Ts D0 T0 := by
  induction h with
  | nil => exact Pairing.nil
  | funnel hm _ ih => exact Pairing.funnel (hs _ hm) ih
  | ground _ ih => exact Pairing.ground ih

theorem KindSeq.mono {d : Decls} {Delta Delta2 : Bounds} (hs : Sub1 Delta Delta2) {Ts : List Ty}
    (h : KindSeq d Delta Ts) : KindSeq d Delta2 Ts := fun T hT => (h T hT).mono hs

theorem SubSeq.mono {d : Decls} {Delta Delta2 : Bounds} (hs : Sub1 Delta Delta2) {Ts Us : List Ty}
    (h : SubSeq d Delta Ts Us) : SubSeq d Delta2 Ts Us := by
  induction h with
  | nil => exact Seq2.nil
  | cons h1 _ ih => exact Seq2.cons (h1.mono hs) ih

theorem Cast.mono {d : Decls} {Delta Delta2 : Bounds} (hs : Sub1 Delta Delta2) {T0 T : Ty}
    (h : Cast d Delta T0 T) : Cast d Delta2 T0 T := by
  induction h with
  | castUp h1 => exact Cast.castUp (h1.mono hs)
  | castVar hm _ ih => exact Cast.castVar (hs _ hm) ih
  | castDown h1 h2 h3 h4 => exact Cast.castDown (h1.mono hs) h2 h3 h4

abbrev innerG (gamma : Gamma) (Fs : List Funnel) (C : ClassName) : Gamma :=
  withoutThis (restrict gamma (Ty.ftvList (abs Fs))) ++ [{ T := .cls C (abs Fs), x := this }]

theorem innerG_sub {gamma gamma2 : Gamma} (h : Sub1 gamma gamma2) (Fs : List Funnel) (C : ClassName) :
    Sub1 (innerG gamma Fs C) (innerG gamma2 Fs C) := by
  intro y hy
  simp only [innerG, withoutThis, restrict, listMem_iff, List.mem_append, List.mem_filter, List.mem_singleton] at hy |-
  rcases hy with hy | hy
  . exact Or.inl (And.intro (And.intro (h y hy.1.1) hy.1.2) hy.2)
  . exact Or.inr hy

theorem innerG_nodup {gamma : Gamma} (h : (gdom gamma).Nodup) (Fs : List Funnel) (C : ClassName) :
    (gdom (innerG gamma Fs C)).Nodup := by
  simp only [innerG, gdom, List.map_append, List.map_cons, List.map_nil]
  apply List.nodup_append.mpr
  refine And.intro (gdom_filter_nodup (gdom_filter_nodup h)) (And.intro (by simp) ?_)
  intro a ha b hb e
  simp only [listMem_iff, List.mem_singleton] at hb
  subst hb
  simp only [listMem_iff, List.mem_map, withoutThis, List.mem_filter] at ha
  rcases ha with ⟨y, hy⟩
  have := hy.1.2
  rw [hy.2, e] at this
  simp at this

theorem innerG_dom {gamma : Gamma} {xs : List VarName} (h : Sub1 (gdom gamma) xs) (Fs : List Funnel) (C : ClassName) :
    Sub1 (gdom (innerG gamma Fs C)) (this :: xs.filter fun x => x != this) := by
  intro y hy
  simp only [innerG, gdom, withoutThis, restrict, listMem_iff, List.map_append, List.mem_append, List.mem_map,
    List.mem_filter, List.mem_singleton, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy |-
  rcases hy with hy | hy
  . cases hy with
    | intro z hz =>
      right
      refine And.intro ?_ ?_
      . rw [<- hz.2]; exact h _ (List.mem_map_of_mem (f := VarDecl.x) hz.1.1.1)
      . rw [<- hz.2]; exact hz.1.2
  . left; exact hy

theorem innerG_dom2 {gamma : Gamma} (Fs : List Funnel) (C : ClassName) :
    Sub1 (gdom (innerG gamma Fs C)) (this :: gdom gamma) := by
  intro y hy
  simp only [innerG, gdom, withoutThis, restrict, listMem_iff, List.map_append, List.mem_append, List.mem_map,
    List.mem_filter, List.mem_singleton, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy |-
  rcases hy with hy | hy
  . cases hy with
    | intro z hz => right; exact Exists.intro z (And.intro hz.1.1.1 hz.2)
  . left; exact hy

theorem gdom_append_single {gamma : Gamma} {T : Ty} {x : VarName} :
    gdom (gamma ++ [{ T := T, x := x }]) = gdom gamma ++ [x] := by simp [gdom]

theorem nodup_snoc {l : List VarName} {x : VarName} (h : l.Nodup) (hx : Not (List.Mem x l)) : (l ++ [x]).Nodup := by
  apply List.nodup_append.mpr
  refine And.intro h (And.intro (by simp) ?_)
  intro a ha b hb e
  simp only [listMem_iff, List.mem_singleton] at hb
  subst hb; subst e
  exact hx ha

mutual
theorem Typing.weak {d : Decls} : forall {Delta gamma e T}, Typing d Delta gamma e T ->
    forall {Delta2 gamma2 Xs xs}, Sub1 Delta Delta2 -> Sub1 gamma gamma2 -> (gdom gamma).Nodup ->
    (gdom gamma2).Nodup -> Sub1 (gdom gamma) xs -> e.noShadow Xs xs = true ->
    (forall y, List.Mem y e.vbinders -> Not (List.Mem y (gdom gamma2))) -> NoThis e -> e.uniq ->
    Typing d Delta2 gamma2 e T
  | _, _, _, _, .subs h hk hs, _, _, _, _, hD, hG, n1, n2, sc, hn, hb, ht, hu =>
    Typing.subs (Typing.weak h hD hG n1 n2 sc hn hb ht hu) (hk.mono hD) (hs.mono hD)
  | _, _, _, _, .var hl, _, _, _, _, _, hG, n1, n2, _, _, _, _, _ =>
    Typing.var (lookup_of_mem_g n2 (hG _ (lookup_mem_g hl)))
  | _, _, _, _, .newObject, _, _, _, _, _, _, _, _, _, _, _, _, _ => Typing.newObject
  | _, _, _, _, .declField h1 h2 h3 h4, _, _, _, _, hD, hG, n1, n2, sc, hn, hb, ht, hu => by
    simp only [Expr.noShadow] at hn
    simp only [Expr.vbinders] at hb
    simp only [NoThis, Expr.vbinders] at ht
    simp only [Expr.uniq] at hu
    exact Typing.declField (Typing.weak h1 hD hG n1 n2 sc hn hb ht hu) h2 h3 h4
  | _, _, _, _, .call h1 h2 h3 h4 h5 h6 h7 h8 h9, _, _, _, _, hD, hG, n1, n2, sc, hn, hb, ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at hb
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq] at hu
    exact Typing.call (Typing.weak h1 hD hG n1 n2 sc hn.1 (fun y hy => hb y (Or.inl hy)) ht.1 hu.1) h2 h3 h4 h5 h6
      (h7.mono hD) (h8.mono hD) (TypingSeq.weak h9 hD hG n1 n2 sc hn.2 (fun y hy => hb y (Or.inr hy)) ht.2 hu.2)
  | _, _, _, _, .callLbRuntime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, _, _, _, _, hD, hG, n1, n2, sc, hn, hb, ht, hu => by
    exact Typing.callLbRuntime (h1.mono hD) h2 h3 h4 h5 h6 h7 (h8.mono hD) (h9.mono hD) (h10.mono hD)
      (TypingSeq.weak h11 hD hG n1 n2 sc (by simpa [Expr.noShadowList, Expr.noShadow] using hn)
        (fun y hy => hb y (by simpa [Expr.vbindersList, Expr.vbinders] using hy))
        (by simpa [NoThis, Expr.vbindersList, Expr.vbinders] using ht)
        (by simpa [Expr.uniqList, Expr.uniq] using hu))
  | _, _, _, _, .newTop h1 h2 h3 h4 h5, _, _, _, _, hD, hG, n1, n2, sc, hn, hb, ht, hu => by
    simp only [Expr.noShadow, noShadowList_append, Bool.and_eq_true] at hn
    simp only [Expr.vbinders, vbindersList_append, listMem_iff, List.mem_append] at hb
    simp only [NoThis, Expr.vbinders, vbindersList_append, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq, uniqList_append] at hu
    exact Typing.newTop h1 (h2.mono hD) h3
      (TypingSeq.weak h4 hD hG n1 n2 sc hn.1 (fun y hy => hb y (Or.inl hy)) ht.1 hu.1)
      (Typing.weak h5 hD hG n1 n2 sc (by simpa [Expr.noShadow] using hn.2)
        (fun y hy => hb y (Or.inr (by simpa [Expr.vbinders] using hy))) (by simpa [NoThis, Expr.vbinders] using ht.2)
        (by simpa [Expr.uniq] using hu.2))
  | _, _, _, _, .newLocal h1 h2 h3 h4 h5 h6 h7 h8, _, _, _, xs, hD, hG, n1, n2, sc, hn, hb, ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at hb
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq] at hu
    refine Typing.newLocal h1 (h2.mono hD) h3 h4 h5
      (Typing.weak h6 hD hG n1 n2 sc (by simpa [Expr.noShadow] using hn.1) (fun y hy => hb y (Or.inl (by simpa [Expr.vbinders] using hy)))
        (by simpa [NoThis, Expr.vbinders] using ht.1) (by simpa [Expr.uniq] using hu.1)) ?_ h8
    intro M hM
    exact MethodOk.weak (h7 M hM) (fun _ h => h) (innerG_sub hG _ _) (innerG_nodup n1 _ _) (innerG_nodup n2 _ _)
      (innerG_dom sc _ _) (noShadowListM_mem hM hn.2)
      (fun y hy hm => by
        have hm2 := innerG_dom2 _ _ y hm
        cases hm2 with
        | head => exact ht.2 (vbindersListM_mem hM hy)
        | tail _ hm2 => exact hb y (Or.inr (vbindersListM_mem hM hy)) hm2)
      (fun h => ht.2 (vbindersListM_mem hM h)) (uniqList_mem hM hu.2)
  | _, _, _, _, .ifInstanceof (x := x) h0 hk hc h1 h2, _, _, _, xs, hD, hG, n1, n2, sc, hn, hb, ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn
    simp only [Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons] at hb
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht
    simp only [Expr.uniq] at hu
    have hxs : Not (List.Mem x xs) := by have := hn.1.1.2; simp at this; exact this
    have hx2 := hb _ (Or.inl (Or.inl (Or.inl rfl)))
    refine Typing.ifInstanceof (Typing.weak h0 hD hG n1 n2 sc hn.1.1.1 (fun y hy => hb y (Or.inl (Or.inl (Or.inr hy))))
      ht.1.1.2 hu.1) (hk.mono hD) ?_ ?_ (Typing.weak h2 hD hG n1 n2 sc hn.2 (fun y hy => hb y (Or.inr hy)) ht.2 hu.2.2)
    . exact Cast.mono hD hc
    . refine Typing.weak h1 hD ?_ ?_ ?_ ?_ hn.1.2 ?_ ht.1.2 hu.2.1
      . intro z hz
        simp only [listMem_iff, List.mem_append, List.mem_singleton] at hz |-
        rcases hz with hz | hz
        . exact Or.inl (hG z hz)
        . exact Or.inr hz
      . rw [gdom_append_single]; exact nodup_snoc n1 (fun h => hxs (sc _ h))
      . rw [gdom_append_single]; exact nodup_snoc n2 hx2
      . rw [gdom_append_single]
        intro z hz
        simp only [listMem_iff, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        . exact List.Mem.tail _ (sc z hz)
        . rw [hz]; exact List.Mem.head _
      . intro y hy hm
        rw [gdom_append_single] at hm
        simp only [listMem_iff, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        . exact hb y (Or.inl (Or.inr hy)) hm
        . exact Expr.noShadow_binders hn.1.2 ht.1.2 y hy (by rw [hm]; exact List.Mem.head _)
theorem TypingSeq.weak {d : Decls} : forall {Delta gamma es Ts}, TypingSeq d Delta gamma es Ts ->
    forall {Delta2 gamma2 Xs xs}, Sub1 Delta Delta2 -> Sub1 gamma gamma2 -> (gdom gamma).Nodup ->
    (gdom gamma2).Nodup -> Sub1 (gdom gamma) xs -> Expr.noShadowList Xs xs es = true ->
    (forall y, List.Mem y (Expr.vbindersList es) -> Not (List.Mem y (gdom gamma2))) ->
    Not (List.Mem this (Expr.vbindersList es)) -> Expr.uniqList es -> TypingSeq d Delta2 gamma2 es Ts
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => TypingSeq.nil
  | _, _, _, _, .cons h hs, _, _, _, _, hD, hG, n1, n2, sc, hn, hb, ht, hu => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at hn
    simp only [Expr.vbindersList, listMem_iff, List.mem_append] at hb
    simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniqList] at hu
    exact TypingSeq.cons (Typing.weak h hD hG n1 n2 sc hn.1 (fun y hy => hb y (Or.inl hy)) ht.1 hu.1)
      (TypingSeq.weak hs hD hG n1 n2 sc hn.2 (fun y hy => hb y (Or.inr hy)) ht.2 hu.2)
theorem MethodOk.weak {d : Decls} : forall {Delta gamma M}, MethodOk d Delta gamma M ->
    forall {Delta2 gamma2 Xs xs}, Sub1 Delta Delta2 -> Sub1 gamma gamma2 -> (gdom gamma).Nodup ->
    (gdom gamma2).Nodup -> Sub1 (gdom gamma) (this :: xs) -> M.noShadow Xs xs = true ->
    (forall y, List.Mem y M.vbinders -> Not (List.Mem y (gdom gamma2))) -> NoThisM M -> M.uniq ->
    MethodOk d Delta2 gamma2 M
  | _, _, _, .methodOk (Delta' := Dm) (ps := ps) h1 h2 h3, _, _, _, xs, hD, hG, n1, n2, sc, hn, hb, ht, hu => by
    simp only [Method.noShadow, Bool.and_eq_true] at hn
    simp only [Method.vbinders, listMem_iff, List.mem_append] at hb
    simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Method.uniq] at hu
    have hD' : Sub1 (_ ++ Dm) (_ ++ Dm) := fun b hb' => by
      simp only [listMem_iff, List.mem_append] at hb' |-
      rcases hb' with hb' | hb'
      . exact Or.inl (hD b hb')
      . exact Or.inr hb'
    have hpx : forall p, List.Mem p (ps.map VarDecl.x) -> Not (List.Mem p xs) :=
      fun p hp => not_mem_of_all_not_contains hn.1.2 hp
    refine MethodOk.methodOk (h1.mono hD') (h2.mono hD') (Typing.weak h3 hD' ?_ ?_ ?_ ?_ hn.2 ?_ ht.2 hu.2.2)
    . intro z hz
      simp only [listMem_iff, List.mem_append] at hz |-
      rcases hz with hz | hz
      . exact Or.inl (hG z hz)
      . exact Or.inr hz
    . simp only [gdom, List.map_append]
      apply List.nodup_append.mpr
      refine And.intro n1 (And.intro hu.2.1 ?_)
      intro a ha b hb' e
      subst e
      have := sc a ha
      cases this with
      | head => exact ht.1 hb'
      | tail _ h => exact hpx a hb' h
    . simp only [gdom, List.map_append]
      apply List.nodup_append.mpr
      refine And.intro n2 (And.intro hu.2.1 ?_)
      intro a ha b hb' e
      subst e
      exact hb a (Or.inl hb') ha
    . intro z hz
      simp only [gdom, List.map_append, listMem_iff, List.mem_append] at hz
      simp only [listMem_iff, List.mem_append, List.mem_cons]
      rcases hz with hz | hz
      . have := sc z hz
        cases this with
        | head => exact Or.inl (Or.inl rfl)
        | tail _ h => exact Or.inl (Or.inr h)
      . exact Or.inr hz
    . intro y hy hm
      simp only [gdom, List.map_append, listMem_iff, List.mem_append] at hm
      rcases hm with hm | hm
      . exact hb y (Or.inr hy) hm
      . exact Expr.noShadow_binders hn.2 ht.2 y hy (List.mem_append_right _ hm)
end

end Funnelling.High