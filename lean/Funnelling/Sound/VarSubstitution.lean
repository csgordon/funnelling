import Funnelling.Sound.Weakening

open Funnelling.SoundSimp

namespace Funnelling

abbrev gsub (n : VSubst) (Gamma : TypeEnv) : TypeEnv := Gamma.filter fun y => !((n.map Prod.fst).contains y.x)

abbrev nthis (n : VSubst) : VSubst := n.filter fun p => p.1 != this

theorem gsub_append {n : VSubst} {g1 g2 : TypeEnv} : gsub n (g1 ++ g2) = gsub n g1 ++ gsub n g2 := by
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
  . simp_all

theorem innerG_gsub {n : VSubst} {Gamma : TypeEnv} {Fs : List Funnel} {C : ClassName} :
    innerG (gsub n Gamma) Fs C = gsub (nthis n) (innerG Gamma Fs C) := by
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
    rw [e2]; simp [Bool.and_comm, Bool.and_assoc]

theorem OverrideOkM.body {d : Decls} {T : Ty} {Delta : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl}
    {e e' : Expr} (h : OverrideOkM d T (.mk Delta T0 m ps e)) : OverrideOkM d T (.mk Delta T0 m ps e') := by
  cases h with
  | absent h1 h2 => exact OverrideOkM.absent h1 h2
  | dec h1 h2 h3 h4 h5 h6 => exact OverrideOkM.dec h1 h2 h3 h4 h5 h6
  | newLocal h1 h2 h3 h4 h5 h6 => exact OverrideOkM.newLocal h1 h2 h3 h4 h5 h6

theorem OverrideOkM.vsubst {d : Decls} {T : Ty} {n : VSubst} {M : Method} (h : OverrideOkM d T M) :
    OverrideOkM d T (M.vsubst n) := by
  cases M with
  | mk Dm T0 m ps e => simp only [Method.vsubst]; exact h.body

theorem names_vsubst {n : VSubst} : forall {Ms : List Method},
    (Method.vsubstList n Ms).map Method.name = Ms.map Method.name
  | [] => rfl
  | M :: Ms => by
    cases M with
    | mk Dm T0 m ps e => simp only [Method.vsubstList, Method.vsubst, List.map_cons, Method.name]; rw [names_vsubst]

theorem Consistent.vsubst {d : Decls} {n n' : VSubst} {C : ClassName} {Fs : List Funnel} {C0 : ClassName}
    {Ts : List Ty} {es : List Expr} {Ms : List Method} (h : Consistent d (.newLocal C Fs C0 Ts es Ms)) :
    Consistent d (.newLocal C Fs C0 Ts (Expr.vsubstList n es) (Method.vsubstList n' Ms)) := by
  rcases consistent_unfold h with ⟨Fs', Ts', es', Ms', h⟩
  refine Exists.intro Fs' (Exists.intro Ts' (Exists.intro es' (Exists.intro Ms' (And.intro h.1
    (And.intro h.2.1 (And.intro h.2.2.1 (And.intro ?_ ?_)))))))
  . intro m; rw [names_vsubst]; exact h.2.2.2.1 m
  . intro M hM
    rcases Method.vsubstList_mem hM with ⟨M0, hM0⟩; rw [hM0.2]; exact (h.2.2.2.2 M0 hM0.1).vsubst

theorem OverrideOk.vsubst {d : Decls} {Delta : Bounds} {T : Ty} {n : VSubst} {Ms : List Method}
    (h : OverrideOk d Delta T Ms) : OverrideOk d Delta T (Method.vsubstList n Ms) := by
  intro M C Ts hM hs
  rcases Method.vsubstList_mem hM with ⟨M0, hM0⟩; rw [hM0.2]; exact (h M0 C Ts hM0.1 hs).vsubst

theorem mem_gsub {n : VSubst} {Gamma : TypeEnv} {y : VarDecl} (h : List.Mem y Gamma)
    (hy : Not (List.Mem y.x (n.map Prod.fst))) : List.Mem y (gsub n Gamma) := by
  simp only [gsub, listMem_iff, List.mem_filter]
  exact And.intro h (by simpa using hy)

abbrev VOk (n : VSubst) : Prop :=
  forall p, List.Mem p n -> p.2.expr.noShadow [] [] = true /\ NoThis p.2.expr /\ p.2.expr.uniq

mutual
theorem Typing.vmap {d : Decls} : forall {Delta Gamma e T}, Typing d Delta Gamma e T ->
    forall {n Delta2 Gamma2 Xs Xs' xs xs'}, Sub1 Delta Delta2 -> Sub1 (gsub n Gamma) Gamma2 -> (gdom Gamma2).Nodup ->
    (forall x v U, List.lookup x n = some v -> Gamma.lookup x = some U -> forall {Delta3 Gamma3 Xs3 xs3},
      (gdom Gamma3).Nodup -> Sub1 (gdom Gamma3) xs3 -> v.expr.noShadow Xs3 xs3 = true -> Typing d Delta3 Gamma3 v.expr U) ->
    (forall y, List.Mem y e.vbinders -> Not (List.Mem y (n.map Prod.fst))) ->
    (gdom Gamma).Nodup -> Sub1 (gdom Gamma) xs -> Sub1 (gdom Gamma2) xs' -> e.noShadow Xs xs = true ->
    (e.vsubst n).noShadow Xs' xs' = true -> NoThis e -> e.uniq -> Typing d Delta2 Gamma2 (e.vsubst n) T
  | _, _, _, _, .subs h hk hs, _, _, _, _, _, _, _, hD, hG, n2, hv, hdef, n1, sc, sc', hn, hn', ht, hu =>
    Typing.subs (Typing.vmap h hD hG n2 hv hdef n1 sc sc' hn hn' ht hu) (hk.mono hD) (hs.mono hD)
  | _, _, _, _, .var (x := x) hl, n, _, _, _, _, _, _, _, hG, n2, hv, _, n1, _, sc', _, hn', _, _ => by
    cases hx : List.lookup x n with
    | none =>
      simp only [Expr.vsubst, hx]
      exact Typing.var (lookup_of_mem_g n2 (hG _ (mem_gsub (lookup_mem_g hl) (lookup_none_not_dom hx))))
    | some v =>
      simp only [Expr.vsubst, hx] at hn' |-
      exact hv x v _ hx hl n2 sc' hn'
  | _, _, _, _, .newObject, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp only [Expr.vsubst, Expr.vsubstList]; exact Typing.newObject
  | _, _, _, _, .declField h1 h2 h3 h4, _, _, _, _, _, _, _, hD, hG, n2, hv, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.vsubst, Expr.noShadow] at hn' |-
    exact Typing.declField (Typing.vmap h1 hD hG n2 hv hdef n1 sc sc' hn hn' ht hu) h2 h3 h4
  | _, _, _, _, .call h1 h2 h3 h4 h5 h6 h7 h8 h9, _, _, _, _, _, _, _, hD, hG, n2, hv, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true] at hn' |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append, NoThis, not_or, Expr.uniq] at hdef ht hu
    exact Typing.call (Typing.vmap h1 hD hG n2 hv (fun y hy => hdef y (Or.inl hy)) n1 sc sc' hn.1 hn'.1 ht.1 hu.1) h2 h3 h4
      h5 h6 (h7.mono hD) (h8.mono hD)
      (TypingSeq.vmap h9 hD hG n2 hv (fun y hy => hdef y (Or.inr hy)) n1 sc sc' hn.2 hn'.2 ht.2 hu.2)
  | _, _, _, _, .callLbRuntime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, _, _, _, _, _, _, _, hD, hG, n2, hv, hdef, n1, sc, sc',
      hn, hn', ht, hu => by
    have := TypingSeq.vmap h11 hD hG n2 hv (fun y hy => hdef y (by simpa [Expr.vbindersList, Expr.vbinders] using hy)) n1 sc
      sc' (by simpa [Expr.noShadowList, Expr.noShadow] using hn)
      (by simp only [Expr.vsubst, Expr.noShadow] at hn'; simpa [Expr.noShadowList, Expr.vsubstList] using hn')
      (by simpa [NoThis, Expr.vbindersList, Expr.vbinders] using ht) (by simpa [Expr.uniqList, Expr.uniq] using hu)
    exact Typing.callLbRuntime (h1.mono hD) h2 h3 h4 h5 h6 h7 (h8.mono hD) (h9.mono hD) (h10.mono hD) this
  | _, _, _, _, .newTop h1 h2 h3 h4 h5, _, _, _, _, _, _, _, hD, hG, n2, hv, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadow, noShadowList_append, Bool.and_eq_true] at hn
    simp only [Expr.vsubst, Expr.vsubstList_append, Expr.noShadow, noShadowList_append, Bool.and_eq_true] at hn' |-
    simp only [Expr.vbinders, vbindersList_append, listMem_iff, List.mem_append, NoThis, not_or, Expr.uniq,
      uniqList_append] at hdef ht hu
    have h5' := Typing.vmap h5 hD hG n2 hv (fun y hy => hdef y (Or.inr (by simpa [Expr.vbinders] using hy))) n1 sc sc'
      (by simpa [Expr.noShadow] using hn.2) (by simpa [Expr.vsubst, Expr.noShadow] using hn'.2)
      (by simpa [NoThis, Expr.vbinders] using ht.2) (by simpa [Expr.uniq] using hu.2)
    exact Typing.newTop h1 (h2.mono hD) h3
      (TypingSeq.vmap h4 hD hG n2 hv (fun y hy => hdef y (Or.inl hy)) n1 sc sc' hn.1 hn'.1 ht.1 hu.1) h5'
  | _, Gamma, _, _, .newLocal (Fs := Fs) (C := C) h1 h2 h3 h4 h5 h6 h7 h8, n, _, Gamma2, _, _, xs, xs', hD, hG, n2, hv, hdef,
      n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true] at hn' |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append, NoThis, not_or, Expr.uniq] at hdef ht hu
    have h6' := Typing.vmap h6 hD hG n2 hv (fun y hy => hdef y (Or.inl (by simpa [Expr.vbinders] using hy))) n1 sc sc'
      (by simpa [Expr.noShadow] using hn.1) (by simpa [Expr.vsubst, Expr.noShadow] using hn'.1)
      (by simpa [NoThis, Expr.vbinders] using ht.1) (by simpa [Expr.uniq] using hu.1)
    refine Typing.newLocal h1.vsubst (h2.mono hD) h3 h4 h5 h6' ?_ h8.vsubst
    intro M' hM'
    rcases Method.vsubstList_mem hM' with ⟨M, hM⟩
    rw [hM.2]
    exact MethodOk.vmap (h7 M hM.1) (n := nthis n) (xs := xs.filter fun x => x != this)
      (xs' := xs'.filter fun x => x != this) (fun _ h => h) (by rw [<- innerG_gsub]; exact innerG_sub hG _ _)
      (innerG_nodup n2 _ _)
      (fun x v U hx hl {_ _ _ _} => by
        have hxt : Not (x = this) := by
          intro e; subst e
          have := (List.mem_filter.mp (lookup_mem hx)).2
          simp at this
        have hl2 : Gamma.lookup x = some U := by
          have hm := lookup_mem_g hl
          simp only [withoutThis, restrict, listMem_iff, List.mem_append, List.mem_filter,
            List.mem_singleton] at hm
          rcases hm with hm | hm
          . exact lookup_of_mem_g n1 hm.1.1
          . simp only [VarDecl.mk.injEq] at hm; exact absurd hm.2 hxt
        rw [lookup_filter_this hxt] at hx
        exact hv x v U hx hl2)
      (fun y hy hm => by
        have hyt : Not (y = this) := fun e => ht.2 (e ▸ Method.mem_vbindersList hM.1 hy)
        exact hdef y (Or.inr (Method.mem_vbindersList hM.1 hy)) ((nthis_dom hyt).mp hm))
      (innerG_nodup n1 _ _) (innerG_dom sc _ _) (innerG_dom sc' _ _)
      (Method.noShadowList_mem hM.1 hn.2)
      (by have := Method.noShadowList_mem hM' hn'.2; rw [hM.2] at this; exact this)
      (fun h => ht.2 (Method.mem_vbindersList hM.1 h)) (Method.uniqList_mem hM.1 hu.2) filter_this_no
  | _, Gamma, _, _, .ifInstanceof (x := x) h0 hk hc h1 h2, n, _, Gamma2, _, _, xs, xs', hD, hG, n2, hv, hdef, n1, sc, sc',
      hn, hn', ht, hu => by
    simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn' |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, NoThis, not_or, Expr.uniq] at hdef ht hu
    have hxs : Not (List.Mem x xs) := by have := hn.1.1.2; simp at this; exact this
    have hxs' : Not (List.Mem x xs') := by have := hn'.1.1.2; simp at this; exact this
    have hxn : Not (List.Mem x (n.map Prod.fst)) := hdef x (Or.inl (Or.inl (Or.inl rfl)))
    refine Typing.ifInstanceof (Typing.vmap h0 hD hG n2 hv (fun y hy => hdef y (Or.inl (Or.inl (Or.inr hy)))) n1 sc sc'
      hn.1.1.1 hn'.1.1.1 ht.1.1.2 hu.1) (hk.mono hD) (hc.mono hD) ?_
      (Typing.vmap h2 hD hG n2 hv (fun y hy => hdef y (Or.inr hy)) n1 sc sc' hn.2 hn'.2 ht.2 hu.2.2)
    refine Typing.vmap h1 (Gamma2 := Gamma2 ++ [{ T := _, x := x }]) hD
      (by rw [gsub_append, gsub_single hxn]; exact Sub1.append _ hG)
      (by rw [gdom_append_single]; exact nodup_snoc n2 (fun h => hxs' (sc' _ h)))
      (fun y v U hy hl {_ _ _ _} => by
        have hyx : Not (y = x) := by intro e; subst e; exact hxn (lookup_some_mem_dom hy)
        have hl2 : Gamma.lookup y = some U := by
          have hm := lookup_mem_g hl
          simp only [listMem_iff, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | hm
          . exact lookup_of_mem_g n1 hm
          . simp only [VarDecl.mk.injEq] at hm; exact absurd hm.2 hyx
        exact hv y v U hy hl2)
      (fun y hy => hdef y (Or.inl (Or.inr hy)))
      (by rw [gdom_append_single]; exact nodup_snoc n1 (fun h => hxs (sc _ h)))
      (scope_snoc sc) (scope_snoc sc') hn.1.2 hn'.1.2 ht.1.2 hu.2.1
theorem TypingSeq.vmap {d : Decls} : forall {Delta Gamma es Ts}, TypingSeq d Delta Gamma es Ts ->
    forall {n Delta2 Gamma2 Xs Xs' xs xs'}, Sub1 Delta Delta2 -> Sub1 (gsub n Gamma) Gamma2 -> (gdom Gamma2).Nodup ->
    (forall x v U, List.lookup x n = some v -> Gamma.lookup x = some U -> forall {Delta3 Gamma3 Xs3 xs3},
      (gdom Gamma3).Nodup -> Sub1 (gdom Gamma3) xs3 -> v.expr.noShadow Xs3 xs3 = true -> Typing d Delta3 Gamma3 v.expr U) ->
    (forall y, List.Mem y (Expr.vbindersList es) -> Not (List.Mem y (n.map Prod.fst))) ->
    (gdom Gamma).Nodup -> Sub1 (gdom Gamma) xs -> Sub1 (gdom Gamma2) xs' -> Expr.noShadowList Xs xs es = true ->
    Expr.noShadowList Xs' xs' (Expr.vsubstList n es) = true ->
    Not (List.Mem this (Expr.vbindersList es)) -> Expr.uniqList es ->
    TypingSeq d Delta2 Gamma2 (Expr.vsubstList n es) Ts
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => TypingSeq.nil
  | _, _, _, _, .cons h hs, _, _, _, _, _, _, _, hD, hG, n2, hv, hdef, n1, sc, sc', hn, hn', ht, hu => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at hn
    simp only [Expr.vsubstList, Expr.noShadowList, Bool.and_eq_true] at hn' |-
    simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or, Expr.uniqList] at hdef ht hu
    exact TypingSeq.cons (Typing.vmap h hD hG n2 hv (fun y hy => hdef y (Or.inl hy)) n1 sc sc' hn.1 hn'.1 ht.1 hu.1)
      (TypingSeq.vmap hs hD hG n2 hv (fun y hy => hdef y (Or.inr hy)) n1 sc sc' hn.2 hn'.2 ht.2 hu.2)
theorem MethodOk.vmap {d : Decls} : forall {Delta Gamma M}, MethodOk d Delta Gamma M ->
    forall {n Delta2 Gamma2 Xs Xs' xs xs'}, Sub1 Delta Delta2 -> Sub1 (gsub n Gamma) Gamma2 -> (gdom Gamma2).Nodup ->
    (forall x v U, List.lookup x n = some v -> Gamma.lookup x = some U -> forall {Delta3 Gamma3 Xs3 xs3},
      (gdom Gamma3).Nodup -> Sub1 (gdom Gamma3) xs3 -> v.expr.noShadow Xs3 xs3 = true -> Typing d Delta3 Gamma3 v.expr U) ->
    (forall y, List.Mem y M.vbinders -> Not (List.Mem y (n.map Prod.fst))) ->
    (gdom Gamma).Nodup -> Sub1 (gdom Gamma) (this :: xs) -> Sub1 (gdom Gamma2) (this :: xs') -> M.noShadow Xs xs = true ->
    (M.vsubst n).noShadow Xs' xs' = true -> NoThisM M -> M.uniq ->
    (forall p, List.Mem p n -> Not (p.1 = this)) -> MethodOk d Delta2 Gamma2 (M.vsubst n)
  | _, Gamma, _, .methodOk (Delta' := Dm) (ps := ps) h1 h2 h3, n, _, Gamma2, _, _, xs, xs', hD, hG, n2, hv, hdef, n1, sc, sc',
      hn, hn', ht, hu, hnt => by
    simp only [Method.noShadow, Bool.and_eq_true] at hn
    simp only [Method.vsubst, Method.noShadow, Bool.and_eq_true] at hn' |-
    simp only [Method.vbinders, listMem_iff, List.mem_append, NoThisM, not_or, Method.uniq] at hdef ht hu
    exact MethodOk.methodOk (h1.mono (Sub1.append _ hD)) (h2.mono (Sub1.append _ hD))
      (Typing.vmap h3 (Gamma2 := Gamma2 ++ ps) (Sub1.append _ hD)
      (by rw [gsub_append, gsub_params (fun p hp => hdef p (Or.inl hp))]; exact Sub1.append _ hG)
      (nodup_params n2 sc' hu.2.1 ht.1 hn'.1.2)
      (fun x v U hx hl {_ _ _ _} => by
        have hxp : Not (List.Mem x (ps.map VarDecl.x)) := fun h => hdef x (Or.inl h) (lookup_some_mem_dom hx)
        have hm := lookup_mem_g hl
        exact (List.mem_append.mp hm).elim (fun hm => hv x v U hx (lookup_of_mem_g n1 hm))
          (fun hm => absurd (List.mem_map_of_mem (f := VarDecl.x) hm) hxp))
      (fun y hy => hdef y (Or.inr hy)) (nodup_params n1 sc hu.2.1 ht.1 hn.1.2) (scope_params sc) (scope_params sc')
      hn.2 hn'.2 ht.2 hu.2.2)
end

mutual
theorem Expr.vsubst_nil : forall (e : Expr), e.vsubst [] = e
  | .var _ => rfl
  | .call e _ _ es => by simp only [Expr.vsubst, Expr.vsubst_nil e, Expr.vsubstList_nil es]
  | .superCall e _ _ _ es => by simp only [Expr.vsubst, Expr.vsubst_nil e, Expr.vsubstList_nil es]
  | .field e _ => by simp only [Expr.vsubst, Expr.vsubst_nil e]
  | .new _ _ es => by simp only [Expr.vsubst, Expr.vsubstList_nil es]
  | .newLocal _ _ _ _ es Ms => by simp only [Expr.vsubst, List.filter_nil, Expr.vsubstList_nil es, Method.vsubstList_nil Ms]
  | .ifInst e0 _ _ e1 e2 => by simp only [Expr.vsubst, Expr.vsubst_nil e0, Expr.vsubst_nil e1, Expr.vsubst_nil e2]
theorem Expr.vsubstList_nil : forall (es : List Expr), Expr.vsubstList [] es = es
  | [] => rfl
  | e :: es => by simp only [Expr.vsubstList, Expr.vsubst_nil e, Expr.vsubstList_nil es]
theorem Method.vsubst_nil : forall (M : Method), M.vsubst [] = M
  | .mk _ _ _ _ e => by simp only [Method.vsubst, Expr.vsubst_nil e]
theorem Method.vsubstList_nil : forall (Ms : List Method), Method.vsubstList [] Ms = Ms
  | [] => rfl
  | M :: Ms => by simp only [Method.vsubstList, Method.vsubst_nil M, Method.vsubstList_nil Ms]
end

theorem Typing.weak {d : Decls} {e : Expr} {U : Ty} (h : Typing d [] [] e U) {Delta Gamma Xs xs}
    (n2 : (gdom Gamma).Nodup) (sc : Sub1 (gdom Gamma) xs) (hn0 : e.noShadow [] [] = true) (ht : NoThis e) (hu : e.uniq)
    (hn : e.noShadow Xs xs = true) : Typing d Delta Gamma e U := by
  have := Typing.vmap h (n := []) (Delta2 := Delta) (Gamma2 := Gamma) (fun _ h => by cases h) (fun _ h => by cases h) n2 (fun _ _ _ h => by cases h)
    (fun _ _ h => by cases h) List.nodup_nil (fun _ h => by cases h) sc hn0 (by rwa [Expr.vsubst_nil]) ht hu
  rwa [Expr.vsubst_nil] at this

theorem Typing.vsub {d : Decls} {Delta Gamma e T} (h : Typing d Delta Gamma e T) {n Xs xs xs'}
    (hv : forall x v U, List.lookup x n = some v -> Gamma.lookup x = some U -> Typing d [] [] v.expr U) (hw : VOk n)
    (hdef : forall y, List.Mem y e.vbinders -> Not (List.Mem y (n.map Prod.fst))) (n1 : (gdom Gamma).Nodup)
    (sc : Sub1 (gdom Gamma) xs) (sc' : Sub1 (gdom (gsub n Gamma)) xs') (hn : e.noShadow Xs xs = true)
    (hn' : (e.vsubst n).noShadow Xs xs' = true) (ht : NoThis e) (hu : e.uniq) :
    Typing d Delta (gsub n Gamma) (e.vsubst n) T :=
  Typing.vmap h (fun _ h => h) (fun _ h => h) (gdom_filter_nodup n1)
    (fun x v U hx hl _ _ _ _ n3 sc3 hn3 =>
      Typing.weak (hv x v U hx hl) n3 sc3 (hw _ (lookup_mem hx)).1 (hw _ (lookup_mem hx)).2.1 (hw _ (lookup_mem hx)).2.2 hn3)
    hdef n1 sc sc' hn hn' ht hu

end Funnelling
