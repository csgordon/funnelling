import Funnelling.Sound.Weak

open Funnelling.SoundSimp

namespace Funnelling.High

abbrev gsub (n : VSubst) (gamma : Gamma) : Gamma := gamma.filter fun y => !((n.map Prod.fst).contains y.x)

abbrev nthis (n : VSubst) : VSubst := n.filter fun p => p.1 != this

theorem gsub_append {n : VSubst} {g1 g2 : Gamma} : gsub n (g1 ++ g2) = gsub n g1 ++ gsub n g2 := by
  simp [gsub, List.filter_append]

theorem gsub_single {n : VSubst} {T : Ty} {x : VarName} (h : Not (List.Mem x (n.map Prod.fst))) :
    gsub n [{ T := T, x := x }] = [{ T := T, x := x }] := by
  have : ((n.map Prod.fst).contains x) = false := by simpa using h
  show List.filter _ [_] = _
  rw [List.filter_cons_of_pos (by simp only [this, Bool.not_false])]
  rfl

theorem gsub_params {n : VSubst} : forall {ps : List VarDecl},
    (forall p, List.Mem p (ps.map VarDecl.x) -> Not (List.Mem p (n.map Prod.fst))) -> gsub n ps = ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [gsub, List.filter_cons]
    have : ((n.map Prod.fst).contains p.x) = false := by simpa using h p.x (List.Mem.head _)
    simp only [this, Bool.not_false, ite_true]
    have ih := gsub_params (n := n) (ps := ps) (fun q hq => h q (List.Mem.tail _ hq))
    simp only [gsub] at ih
    rw [ih]

theorem nthis_dom {n : VSubst} {y : VarName} (hy : Not (y = this)) :
    List.Mem y ((nthis n).map Prod.fst) <-> List.Mem y (n.map Prod.fst) := by
  simp only [nthis, listMem_iff, List.mem_map, List.mem_filter]
  constructor
  . intro h; cases h with | intro p hp => exact Exists.intro p (And.intro hp.1.1 hp.2)
  . intro h
    rcases h with ⟨p, hp⟩
    refine Exists.intro p (And.intro (And.intro hp.1 ?_) hp.2)
    rw [hp.2]; simpa using hy

theorem innerG_gsub {n : VSubst} {gamma : Gamma} {Fs : List Funnel} {C : ClassName} :
    innerG (gsub n gamma) Fs C = gsub (nthis n) (innerG gamma Fs C) := by
  simp only [innerG, gsub_append]
  rw [gsub_single (by intro h; have := List.mem_map.mp h; cases this with | intro p hp =>
    have h2 := (List.mem_filter.mp hp.1).2; rw [hp.2] at h2; simp at h2)]
  congr 1
  simp only [withoutThis, restrict, gsub, List.filter_filter]
  apply List.filter_congr
  intro y _
  by_cases hy : y.x = this
  . simp [hy]
  . have e := nthis_dom (n := n) hy
    have e2 : ((nthis n).map Prod.fst).contains y.x = (n.map Prod.fst).contains y.x := by
      rw [Bool.eq_iff_iff]; simp only [List.contains_iff_mem]; exact e
    rw [e2]; simp [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

theorem Expr.vsubstList_append {n : VSubst} : forall {es1 es2 : List Expr},
    Expr.vsubstList n (es1 ++ es2) = Expr.vsubstList n es1 ++ Expr.vsubstList n es2
  | [], _ => rfl
  | e :: es1, es2 => by simp only [List.cons_append, Expr.vsubstList]; rw [Expr.vsubstList_append]

theorem OverrideOkM.body {d : Decls} {T : Ty} {Delta : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl}
    {e e' : Expr} (h : OverrideOkM d T (.mk Delta T0 m ps e)) : OverrideOkM d T (.mk Delta T0 m ps e') := by
  cases h with
  | absent h1 h2 => exact OverrideOkM.absent h1 h2
  | dec h1 h2 h3 h4 h5 h6 => exact OverrideOkM.dec h1 h2 h3 h4 h5 h6
  | loc h1 h2 h3 h4 h5 h6 => exact OverrideOkM.loc h1 h2 h3 h4 h5 h6

theorem OverrideOkM.vsubst {d : Decls} {T : Ty} {n : VSubst} {M : Method} (h : OverrideOkM d T M) :
    OverrideOkM d T (M.vsubst n) := by
  cases M with
  | mk Dm T0 m ps e => simp only [Method.vsubst]; exact h.body

theorem vsubstList_mem {n : VSubst} {M : Method} : forall {Ms : List Method}, List.Mem M (Method.vsubstList n Ms) ->
    exists M0, List.Mem M0 Ms /\ M = M0.vsubst n
  | [], h => by cases h
  | M' :: Ms, h => by
    simp only [Method.vsubstList] at h
    cases h with
    | head => exact Exists.intro M' (And.intro (List.Mem.head _) rfl)
    | tail _ h =>
      rcases vsubstList_mem h with ⟨M0, hM0⟩; exact Exists.intro M0 (And.intro (List.Mem.tail _ hM0.1) hM0.2)

theorem names_vsubst {n : VSubst} : forall {Ms : List Method},
    (Method.vsubstList n Ms).map Method.name = Ms.map Method.name
  | [] => rfl
  | M :: Ms => by
    cases M with
    | mk Dm T0 m ps e => simp only [Method.vsubstList, Method.vsubst, List.map_cons, Method.name]; rw [names_vsubst]

theorem Consistent.vsubst {d : Decls} {n n' : VSubst} {C : ClassName} {Fs : List Funnel} {C0 : ClassName}
    {Ts : List Ty} {es : List Expr} {Ms : List Method} (h : Consistent d (.loc C Fs C0 Ts es Ms)) :
    Consistent d (.loc C Fs C0 Ts (Expr.vsubstList n es) (Method.vsubstList n' Ms)) := by
  cases consistent_unfold h with
  | intro Fs' h => cases h with
    | intro Ts' h => cases h with
      | intro es' h => cases h with
        | intro Ms' h =>
          refine Exists.intro Fs' (Exists.intro Ts' (Exists.intro es' (Exists.intro Ms' (And.intro h.1
            (And.intro h.2.1 (And.intro h.2.2.1 (And.intro ?_ ?_)))))))
          . intro m; rw [names_vsubst]; exact h.2.2.2.1 m
          . intro M hM
            rcases vsubstList_mem hM with ⟨M0, hM0⟩; rw [hM0.2]; exact (h.2.2.2.2 M0 hM0.1).vsubst

theorem OverrideOk.vsubst {d : Decls} {Delta : Bounds} {T : Ty} {n : VSubst} {Ms : List Method}
    (h : OverrideOk d Delta T Ms) : OverrideOk d Delta T (Method.vsubstList n Ms) := by
  intro M C Ts hM hs
  rcases vsubstList_mem hM with ⟨M0, hM0⟩; rw [hM0.2]; exact (h M0 C Ts hM0.1 hs).vsubst

theorem lookup_none_not_dom {n : VSubst} {x : VarName} (h : List.lookup x n = none) :
    Not (List.Mem x (n.map Prod.fst)) := by
  intro hm
  rcases lookup_isSome hm with ⟨v, hv⟩; rw [hv] at h; cases h

theorem mem_gsub {n : VSubst} {gamma : Gamma} {y : VarDecl} (h : List.Mem y gamma)
    (hy : Not (List.Mem y.x (n.map Prod.fst))) : List.Mem y (gsub n gamma) := by
  simp only [gsub, listMem_iff, List.mem_filter]
  exact And.intro h (by simpa using hy)

abbrev VOk (n : VSubst) : Prop :=
  forall p, List.Mem p n -> p.2.expr.noShadow [] [] = true /\ NoThis p.2.expr /\ p.2.expr.uniq

theorem VOk.nthis {n : VSubst} (h : VOk n) : VOk (nthis n) := fun p hp => h p (List.mem_filter.mp hp).1

mutual
theorem Typing.vsub {d : Decls} : forall {Delta gamma e T}, Typing d Delta gamma e T ->
    forall {n Xs xs xs'}, (forall x v U, List.lookup x n = some v -> gamma.lookup x = some U -> Typing d [] [] v.expr U) ->
    VOk n -> (forall y, List.Mem y e.vbinders -> Not (List.Mem y (n.map Prod.fst))) ->
    (gdom gamma).Nodup -> Sub1 (gdom gamma) xs -> Sub1 (gdom (gsub n gamma)) xs' -> e.noShadow Xs xs = true ->
    (e.vsubst n).noShadow Xs xs' = true ->
    NoThis e -> e.uniq -> Typing d Delta (gsub n gamma) (e.vsubst n) T
  | _, _, _, _, .subs h hk hs, _, _, _, _, hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu =>
    Typing.subs (Typing.vsub h hv hw hdef n1 sc sc' hn hn' ht hu) hk hs
  | _, _, _, _, .var (x := x) hl, n, _, _, _, hv, hw, _, n1, sc, sc', _, hn', _, _ => by
    cases hx : List.lookup x n with
    | none =>
      simp only [Expr.vsubst, hx]
      exact Typing.var (lookup_of_mem_g (gdom_filter_nodup n1) (mem_gsub (lookup_mem_g hl) (lookup_none_not_dom hx)))
    | some v =>
      simp only [Expr.vsubst, hx] at hn' |-
      have hvw := hw (x, v) (lookup_mem hx)
      exact Typing.weak (hv x v _ hx hl) (fun _ h => by cases h) (fun _ h => by cases h) List.nodup_nil
        (gdom_filter_nodup n1) (fun _ h => by cases h) hvw.1
        (fun y hy hm => Expr.noShadow_binders hn' hvw.2.1 y hy (sc' y hm)) hvw.2.1 hvw.2.2
  | _, _, _, _, .newObject, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp only [Expr.vsubst, Expr.vsubstList]; exact Typing.newObject
  | _, _, _, _, .declField h1 h2 h3 h4, _, _, _, _, hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadow] at hn
    simp only [Expr.vsubst, Expr.noShadow] at hn' |-
    simp only [Expr.vbinders] at hdef
    simp only [NoThis, Expr.vbinders] at ht
    simp only [Expr.uniq] at hu
    exact Typing.declField (Typing.vsub h1 hv hw hdef n1 sc sc' hn hn' ht hu) h2 h3 h4
  | _, _, _, _, .call h1 h2 h3 h4 h5 h6 h7 h8 h9, _, _, _, _, hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true] at hn' |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at hdef
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq] at hu
    exact Typing.call (Typing.vsub h1 hv hw (fun y hy => hdef y (Or.inl hy)) n1 sc sc' hn.1 hn'.1 ht.1 hu.1) h2 h3 h4 h5 h6 h7 h8
      (TypingSeq.vsub h9 hv hw (fun y hy => hdef y (Or.inr hy)) n1 sc sc' hn.2 hn'.2 ht.2 hu.2)
  | _, _, _, _, .callLbRuntime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, _, _, _, _, hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.vsubst]
    have := TypingSeq.vsub h11 hv hw (fun y hy => hdef y (by simpa [Expr.vbindersList, Expr.vbinders] using hy)) n1 sc sc'
      (by simpa [Expr.noShadowList, Expr.noShadow] using hn)
      (by simp only [Expr.vsubst, Expr.noShadow] at hn'; simpa [Expr.noShadowList, Expr.vsubstList] using hn')
      (by simpa [NoThis, Expr.vbindersList, Expr.vbinders] using ht) (by simpa [Expr.uniqList, Expr.uniq] using hu)
    simp only [Expr.vsubstList] at this
    exact Typing.callLbRuntime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 this
  | _, _, _, _, .newTop h1 h2 h3 h4 h5, _, _, _, _, hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadow, noShadowList_append, Bool.and_eq_true] at hn
    simp only [Expr.vsubst, Expr.vsubstList_append, Expr.noShadow, noShadowList_append, Bool.and_eq_true] at hn' |-
    simp only [Expr.vbinders, vbindersList_append, listMem_iff, List.mem_append] at hdef
    simp only [NoThis, Expr.vbinders, vbindersList_append, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq, uniqList_append] at hu
    have h5' := Typing.vsub h5 hv hw (fun y hy => hdef y (Or.inr (by simpa [Expr.vbinders] using hy))) n1 sc sc'
      (by simpa [Expr.noShadow] using hn.2) (by simpa [Expr.vsubst, Expr.noShadow] using hn'.2)
      (by simpa [NoThis, Expr.vbinders] using ht.2) (by simpa [Expr.uniq] using hu.2)
    simp only [Expr.vsubst] at h5'
    exact Typing.newTop h1 h2 h3 (TypingSeq.vsub h4 hv hw (fun y hy => hdef y (Or.inl hy)) n1 sc sc' hn.1 hn'.1 ht.1 hu.1) h5'
  | _, gamma, _, _, .newLocal (Fs := Fs) (C := C) h1 h2 h3 h4 h5 h6 h7 h8, n, _, xs, xs', hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true] at hn' |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at hdef
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniq] at hu
    have h6' := Typing.vsub h6 hv hw (fun y hy => hdef y (Or.inl (by simpa [Expr.vbinders] using hy))) n1 sc sc'
      (by simpa [Expr.noShadow] using hn.1) (by simpa [Expr.vsubst, Expr.noShadow] using hn'.1)
      (by simpa [NoThis, Expr.vbinders] using ht.1) (by simpa [Expr.uniq] using hu.1)
    simp only [Expr.vsubst] at h6'
    refine Typing.newLocal h1.vsubst h2 h3 h4 h5 h6' ?_ h8.vsubst
    intro M' hM'
    rcases vsubstList_mem hM' with ⟨M, hM⟩
    rw [hM.2]
    have hmo := MethodOk.vsub (h7 M hM.1) (n := nthis n) (xs := xs.filter fun x => x != this)
      (xs' := xs'.filter fun x => x != this)
      (fun x v U hx hl => by
        have hxt : Not (x = this) := by
          intro e; subst e
          have := (List.mem_filter.mp (lookup_mem hx)).2
          simp at this
        have hl2 : gamma.lookup x = some U := by
          have hm := lookup_mem_g hl
          simp only [innerG, withoutThis, restrict, listMem_iff, List.mem_append, List.mem_filter,
            List.mem_singleton] at hm
          rcases hm with hm | hm
          . exact lookup_of_mem_g n1 hm.1.1
          . simp only [VarDecl.mk.injEq] at hm; exact absurd hm.2 hxt
        rw [lookup_filter_this hxt] at hx
        exact hv x v U hx hl2)
      hw.nthis (fun y hy hm => by
        have hyt : Not (y = this) := fun e => ht.2 (e ▸ vbindersListM_mem hM.1 hy)
        exact hdef y (Or.inr (vbindersListM_mem hM.1 hy)) ((nthis_dom hyt).mp hm))
      (innerG_nodup n1 _ _) (innerG_dom sc _ _) (by rw [<- innerG_gsub]; exact innerG_dom sc' _ _)
      (noShadowListM_all hn.2 hM.1)
      (by have := noShadowListM_all hn'.2 hM'; rw [hM.2] at this; exact this)
      (fun h => ht.2 (vbindersListM_mem hM.1 h)) (uniqList_mem hM.1 hu.2) filter_this_no
    show MethodOk _ _ (innerG (gsub n gamma) Fs C) _
    rw [innerG_gsub]
    exact hmo
  | _, gamma, _, _, .ifInstanceof (x := x) h0 hk hc h1 h2, n, _, xs, xs', hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn' |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons] at hdef
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht
    simp only [Expr.uniq] at hu
    have hxs : Not (List.Mem x xs) := by have := hn.1.1.2; simp at this; exact this
    have hxn : Not (List.Mem x (n.map Prod.fst)) := hdef x (Or.inl (Or.inl (Or.inl rfl)))
    refine Typing.ifInstanceof (Typing.vsub h0 hv hw (fun y hy => hdef y (Or.inl (Or.inl (Or.inr hy)))) n1 sc sc' hn.1.1.1
      hn'.1.1.1 ht.1.1.2 hu.1) hk hc ?_ (Typing.vsub h2 hv hw (fun y hy => hdef y (Or.inr hy)) n1 sc sc' hn.2 hn'.2 ht.2 hu.2.2)
    have h1' := Typing.vsub h1 (n := n) (xs := x :: xs) (xs' := x :: xs')
      (fun y v U hy hl => by
        have hyx : Not (y = x) := by intro e; subst e; exact hxn (lookup_some_mem_dom hy)
        have hl2 : gamma.lookup y = some U := by
          have hm := lookup_mem_g hl
          simp only [listMem_iff, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | hm
          . exact lookup_of_mem_g n1 hm
          . simp only [VarDecl.mk.injEq] at hm; exact absurd hm.2 hyx
        exact hv y v U hy hl2)
      hw (fun y hy => hdef y (Or.inl (Or.inr hy)))
      (by rw [gdom_append_single]; exact nodup_snoc n1 (fun h => hxs (sc _ h)))
      (by
        rw [gdom_append_single]
        intro z hz
        simp only [listMem_iff, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        . exact List.Mem.tail _ (sc z hz)
        . rw [hz]; exact List.Mem.head _)
      (by
        rw [gsub_append, gsub_single hxn, gdom_append_single]
        intro z hz
        simp only [listMem_iff, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        . exact List.Mem.tail _ (sc' z hz)
        . rw [hz]; exact List.Mem.head _)
      hn.1.2 hn'.1.2 ht.1.2 hu.2.1
    rw [gsub_append, gsub_single hxn] at h1'
    exact h1'
theorem TypingSeq.vsub {d : Decls} : forall {Delta gamma es Ts}, TypingSeq d Delta gamma es Ts ->
    forall {n Xs xs xs'}, (forall x v U, List.lookup x n = some v -> gamma.lookup x = some U -> Typing d [] [] v.expr U) ->
    VOk n -> (forall y, List.Mem y (Expr.vbindersList es) -> Not (List.Mem y (n.map Prod.fst))) ->
    (gdom gamma).Nodup -> Sub1 (gdom gamma) xs -> Sub1 (gdom (gsub n gamma)) xs' -> Expr.noShadowList Xs xs es = true ->
    Expr.noShadowList Xs xs' (Expr.vsubstList n es) = true ->
    Not (List.Mem this (Expr.vbindersList es)) -> Expr.uniqList es ->
    TypingSeq d Delta (gsub n gamma) (Expr.vsubstList n es) Ts
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => TypingSeq.nil
  | _, _, _, _, .cons h hs, _, _, _, _, hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at hn
    simp only [Expr.vsubstList, Expr.noShadowList, Bool.and_eq_true] at hn' |-
    simp only [Expr.vbindersList, listMem_iff, List.mem_append] at hdef
    simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ht
    simp only [Expr.uniqList] at hu
    exact TypingSeq.cons (Typing.vsub h hv hw (fun y hy => hdef y (Or.inl hy)) n1 sc sc' hn.1 hn'.1 ht.1 hu.1)
      (TypingSeq.vsub hs hv hw (fun y hy => hdef y (Or.inr hy)) n1 sc sc' hn.2 hn'.2 ht.2 hu.2)
theorem MethodOk.vsub {d : Decls} : forall {Delta gamma M}, MethodOk d Delta gamma M ->
    forall {n Xs xs xs'}, (forall x v U, List.lookup x n = some v -> gamma.lookup x = some U -> Typing d [] [] v.expr U) ->
    VOk n -> (forall y, List.Mem y M.vbinders -> Not (List.Mem y (n.map Prod.fst))) ->
    (gdom gamma).Nodup -> Sub1 (gdom gamma) (this :: xs) -> Sub1 (gdom (gsub n gamma)) (this :: xs') -> M.noShadow Xs xs = true ->
    (M.vsubst n).noShadow Xs xs' = true -> NoThisM M -> M.uniq ->
    (forall p, List.Mem p n -> Not (p.1 = this)) -> MethodOk d Delta (gsub n gamma) (M.vsubst n)
  | _, gamma, _, .methodOk (Delta' := Dm) (ps := ps) h1 h2 h3, n, _, xs, xs', hv, hw, hdef, n1, sc, sc', hn, hn', ht, hu, hnt => by
    simp only [Method.noShadow, Bool.and_eq_true] at hn
    simp only [Method.vsubst, Method.noShadow, Bool.and_eq_true] at hn' |-
    simp only [Method.vbinders, listMem_iff, List.mem_append] at hdef
    simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Method.uniq] at hu
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
    have hb := Typing.vsub h3 (n := n) (xs := this :: xs ++ ps.map VarDecl.x) (xs' := this :: xs' ++ ps.map VarDecl.x)
      (fun x v U hx hl => by
        have hxp : Not (List.Mem x (ps.map VarDecl.x)) := fun h => hdef x (Or.inl h) (lookup_some_mem_dom hx)
        have hm := lookup_mem_g hl
        simp only [listMem_iff, List.mem_append] at hm
        rcases hm with hm | hm
        . exact hv x v U hx (lookup_of_mem_g n1 hm)
        . exact absurd (List.mem_map_of_mem (f := VarDecl.x) hm) hxp)
      hw (fun y hy => hdef y (Or.inr hy)) hnod
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
      (by
        rw [gsub_append, gsub_params (fun p hp => hdef p (Or.inl hp))]
        intro z hz
        simp only [gdom, List.map_append, listMem_iff, List.mem_append] at hz
        simp only [listMem_iff, List.mem_append, List.mem_cons]
        rcases hz with hz | hz
        . have := sc' z hz
          cases this with
          | head => exact Or.inl (Or.inl rfl)
          | tail _ h => exact Or.inl (Or.inr h)
        . exact Or.inr hz)
      hn.2 hn'.2 ht.2 hu.2.2
    rw [gsub_append, gsub_params (fun p hp => hdef p (Or.inl hp))] at hb
    exact MethodOk.methodOk h1 h2 hb
end

end Funnelling.High