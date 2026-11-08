import Funnelling.Sound.Uniq

open Funnelling.SoundSimp

namespace Funnelling.High

structure CompEnv (rv1 rv2 rv3 : VRen) (rt1 rt2 rt3 : TRen) (Sa Sb : List VarName)
    (Ta Tb : List TVarName) : Prop where
  sv : forall w, List.Mem w Sa -> Not (w = this) -> List.Mem (rn rv1 w) Sb /\ rn rv2 (rn rv1 w) = rn rv3 w
  st : forall X, List.Mem X Ta -> List.Mem (rn rt1 X) Tb /\ rn rt2 (rn rt1 X) = rn rt3 X
  k1 : forall p, List.Mem p rv1 -> Not (p.1 = this) /\ Not (p.2 = this)
  k2 : forall p, List.Mem p rv2 -> Not (p.1 = this)
  k3 : forall p, List.Mem p rv3 -> Not (p.1 = this)

theorem CompEnv.tys {rv1 rv2 rv3 : VRen} {rt1 rt2 rt3 : TRen} {Sa Sb Ta Tb}
    (env : CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb) {Ts : List Ty}
    (h : (Ty.ftvList Ts).all Ta.contains = true) :
    Ty.renList rt2 (Ty.renList rt1 Ts) = Ty.renList rt3 Ts :=
  Ty.renList_comp (fun X hX => (env.st X (all_contains_iff.mp h X hX)).2)

theorem CompEnv.ty {rv1 rv2 rv3 : VRen} {rt1 rt2 rt3 : TRen} {Sa Sb Ta Tb}
    (env : CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb) {T : Ty}
    (h : T.ftv.all Ta.contains = true) : (T.ren rt1).ren rt2 = T.ren rt3 :=
  Ty.ren_comp (fun X hX => (env.st X (all_contains_iff.mp h X hX)).2)

theorem CompEnv.ifExt {rv1 rv2 rv3 : VRen} {rt1 rt2 rt3 : TRen} {Sa Sb Ta Tb}
    (env : CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb) {x y z : VarName}
    (hx : Not (x = this)) (hy : Not (y = this)) (hyS : Not (List.Mem y Sb)) :
    CompEnv ((x, y) :: rv1) ((y, z) :: rv2) ((x, z) :: rv3) rt1 rt2 rt3 (x :: Sa) (y :: Sb) Ta Tb where
  sv := by
    intro w hw hwt
    by_cases e : w = x
    . subst e; rw [rn_cons_eq, rn_cons_eq, rn_cons_eq]; exact And.intro (List.Mem.head _) rfl
    . have hwS : List.Mem w Sa := by
        cases hw with
        | head => exact absurd rfl e
        | tail _ h => exact h
      have r := env.sv w hwS hwt
      have hne : Not (rn rv1 w = y) := fun e' => hyS (e' ▸ r.1)
      rw [rn_cons_ne e, rn_cons_ne hne, rn_cons_ne e]
      exact And.intro (List.Mem.tail _ r.1) r.2
  st := env.st
  k1 := by
    intro p hp
    cases hp with
    | head => exact And.intro hx hy
    | tail _ hp => exact env.k1 p hp
  k2 := by
    intro p hp
    cases hp with
    | head => exact hy
    | tail _ hp => exact env.k2 p hp
  k3 := by
    intro p hp
    cases hp with
    | head => exact hx
    | tail _ hp => exact env.k3 p hp

theorem CompEnv.filt {rv1 rv2 rv3 : VRen} {rt1 rt2 rt3 : TRen} {Sa Sb Ta Tb}
    (env : CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb) :
    CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa (Sb.filter fun x => x != this) Ta Tb where
  sv := by
    intro w hw hwt
    have r := env.sv w hw hwt
    have hne := rn_ne_this (fun p hp => (env.k1 p hp).2) hwt
    refine And.intro ?_ r.2
    simp only [listMem_iff, List.mem_filter] at r |-
    exact And.intro r.1 (by simpa using hne)
  st := env.st
  k1 := env.k1
  k2 := env.k2
  k3 := env.k3

theorem not_mem_of_all_not_contains {A : Type} [DecidableEq A] {l xs : List A}
    (h : l.all (fun x => !(xs.contains x)) = true) {x : A} (hx : List.Mem x l) : Not (List.Mem x xs) := by
  rw [List.all_eq_true] at h
  have h2 := h x hx
  simp at h2
  exact h2

theorem CompEnv.methExt {rv1 rv2 rv3 : VRen} {rt1 rt2 rt3 : TRen} {Sa Sb Ta Tb}
    (env : CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb) {xa xb xc : List VarName}
    {Xa Xb Xc : List TVarName}
    (hla : xa.length = xb.length) (hlb : xb.length = xc.length) (hnb : xb.Nodup)
    (hLa : Xa.length = Xb.length) (hLb : Xb.length = Xc.length) (hNb : Xb.Nodup)
    (hta : Not (List.Mem this xa)) (htb : Not (List.Mem this xb))
    (hxb : xb.all (fun x => !(Sb.contains x)) = true)
    (hXb : Xb.all (fun X => !(Tb.contains X)) = true) :
    CompEnv (xa.zip xb ++ rv1) (xb.zip xc ++ rv2) (xa.zip xc ++ rv3)
      (Xa.zip Xb ++ rt1) (Xb.zip Xc ++ rt2) (Xa.zip Xc ++ rt3)
      (this :: Sa ++ xa) (this :: Sb ++ xb) (Ta ++ Xa) (Tb ++ Xb) where
  sv := by
    intro w hw hwt
    by_cases hm : List.Mem w xa
    . refine And.intro ?_ (rn_zip_comp hla hlb hnb hm)
      exact List.mem_append_right _ (rn_zip_mem hla hm)
    . have hwS : List.Mem w Sa := by
        simp only [listMem_iff, List.mem_append, List.mem_cons] at hw hm
        rcases hw with (h | h) | h
        . exact absurd h hwt
        . exact h
        . exact absurd h hm
      have r := env.sv w hwS hwt
      rw [rn_zip_not_mem hm, rn_zip_not_mem hm]
      have hnot : Not (List.Mem (rn rv1 w) xb) := by
        intro h'
        exact not_mem_of_all_not_contains hxb h' r.1
      rw [rn_zip_not_mem hnot]
      refine And.intro ?_ r.2
      exact List.mem_append_left _ (List.Mem.tail _ r.1)
  st := by
    intro X hX
    by_cases hm : List.Mem X Xa
    . refine And.intro ?_ (rn_zip_comp hLa hLb hNb hm)
      exact List.mem_append_right _ (rn_zip_mem hLa hm)
    . have hXT : List.Mem X Ta := by
        simp only [listMem_iff, List.mem_append] at hX hm
        rcases hX with h | h
        . exact h
        . exact absurd h hm
      have r := env.st X hXT
      rw [rn_zip_not_mem hm, rn_zip_not_mem hm]
      have hnot : Not (List.Mem (rn rt1 X) Xb) := by
        intro h'
        exact not_mem_of_all_not_contains hXb h' r.1
      rw [rn_zip_not_mem hnot]
      exact And.intro (List.mem_append_left _ r.1) r.2
  k1 := by
    intro p hp
    simp only [listMem_iff, List.mem_append] at hp
    rcases hp with hp | hp
    . have h1 := List.of_mem_zip hp
      exact And.intro (fun e => hta (e ▸ h1.1)) (fun e => htb (e ▸ h1.2))
    . exact env.k1 p hp
  k2 := by
    intro p hp
    exact (List.mem_append.mp hp).elim (fun hp => fun e => htb (e ▸ (List.of_mem_zip hp).1)) (env.k2 p)
  k3 := by
    intro p hp
    exact (List.mem_append.mp hp).elim (fun hp => fun e => hta (e ▸ (List.of_mem_zip hp).1)) (env.k3 p)

theorem dom_renBounds {r : TRen} : forall {Delta : Bounds} {Xs : List TVarName},
    Xs.length = Delta.length ->
    dom ((Delta.zip Xs).map fun p => ({ X := p.2, T := p.1.T.ren r } : Bound)) = Xs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | b :: Delta, X :: Xs, h => by
    simp only [List.zip_cons_cons, List.map_cons, dom] at |-
    rw [show List.map Bound.X (List.map (fun p => ({ X := p.2, T := p.1.T.ren r } : Bound)) (Delta.zip Xs)) =
      dom ((Delta.zip Xs).map fun p => ({ X := p.2, T := p.1.T.ren r } : Bound)) from rfl,
      dom_renBounds (by simpa using h)]

theorem names_renParams {r : TRen} : forall {ps : List VarDecl} {xs : List VarName},
    xs.length = ps.length ->
    ((ps.zip xs).map fun p => ({ T := p.1.T.ren r, x := p.2 } : VarDecl)).map VarDecl.x = xs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, x :: xs, h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [names_renParams (by simpa using h)]

theorem bounds_comp {r1 r2 r3 : TRen} : forall {Delta : Bounds} {Xs1 Xs2 : List TVarName},
    Xs1.length = Delta.length -> Xs2.length = Delta.length ->
    (forall b, List.Mem b Delta -> (b.T.ren r1).ren r2 = b.T.ren r3) ->
    (((Delta.zip Xs1).map fun p => ({ X := p.2, T := p.1.T.ren r1 } : Bound)).zip Xs2).map
        (fun p => ({ X := p.2, T := p.1.T.ren r2 } : Bound)) =
      (Delta.zip Xs2).map fun p => ({ X := p.2, T := p.1.T.ren r3 } : Bound)
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], _, _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _, [], _, h, _ => by simp at h
  | b :: Delta, X1 :: Xs1, X2 :: Xs2, h1, h2, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine And.intro ?_ (bounds_comp (by simpa using h1) (by simpa using h2)
      (fun b' hb' => h b' (List.Mem.tail _ hb')))
    rw [h b (List.Mem.head _)]

theorem params_comp {r1 r2 r3 : TRen} : forall {ps : List VarDecl} {xs1 xs2 : List VarName},
    xs1.length = ps.length -> xs2.length = ps.length ->
    (forall p, List.Mem p ps -> (p.T.ren r1).ren r2 = p.T.ren r3) ->
    (((ps.zip xs1).map fun p => ({ T := p.1.T.ren r1, x := p.2 } : VarDecl)).zip xs2).map
        (fun p => ({ T := p.1.T.ren r2, x := p.2 } : VarDecl)) =
      (ps.zip xs2).map fun p => ({ T := p.1.T.ren r3, x := p.2 } : VarDecl)
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => by simp at h
  | [], _, _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _, [], _, h, _ => by simp at h
  | p :: ps, x1 :: xs1, x2 :: xs2, h1, h2, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine And.intro ?_ (params_comp (by simpa using h1) (by simpa using h2)
      (fun p' hp' => h p' (List.Mem.tail _ hp')))
    rw [h p (List.Mem.head _)]

theorem ftvList_append {Ts Us : List Ty} : Ty.ftvList (Ts ++ Us) = Ty.ftvList Ts ++ Ty.ftvList Us := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih => simp [Ty.ftvList, ih]

theorem ftvList_map_mem {A : Type} {f : A -> Ty} {l : List A} {a : A} (ha : List.Mem a l) {X : TVarName}
    (hX : List.Mem X (f a).ftv) : List.Mem X (Ty.ftvList (l.map f)) := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    cases ha with
    | head => exact List.mem_append_left _ hX
    | tail _ h => exact List.mem_append_right _ (ih h)

mutual
theorem RenE.comp {rv1 rt1 a b} : RenE rv1 rt1 a b -> forall {rv2 rt2 c rv3 rt3 Sa Sb Ta Tb},
    RenE rv2 rt2 b c -> CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb -> a.closed Ta Sa = true ->
    b.noShadow Tb Sb = true -> NoThis a -> NoThis b -> b.uniq -> RenE rv3 rt3 a c
  | .var (x := x), rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, _, _, _, _ => by
    cases h2
    simp only [Expr.closed] at hc
    have hx : List.Mem x Sa := by simpa using hc
    have e : (x.ren rv1).ren rv2 = x.ren rv3 := by
      simp only [VarName.ren_eq]
      by_cases ht : x = this
      . subst ht
        rw [rn_this (fun p hp => (env.k1 p hp).1), rn_this env.k2, rn_this env.k3]
      . exact (env.sv x hx ht).2
    rw [e]; exact RenE.var
  | .call (Ts := Ts) (m := m) h1 hs1, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | call h2 hs2 =>
      simp only [Expr.closed, Bool.and_eq_true, Expr.noShadow] at hc hn
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
      simp only [Expr.uniq] at hu
      rw [env.tys hc.1.2]
      exact RenE.call (RenE.comp h1 h2 env hc.1.1 hn.1 ha.1 hb.1 hu.1)
        (RenEs.comp hs1 hs2 env hc.2 hn.2 ha.2 hb.2 hu.2)
  | .superCall (T := T) (Ts := Ts) h1 hs1, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | superCall h2 hs2 =>
      simp only [Expr.closed, Bool.and_eq_true, Expr.noShadow] at hc hn
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
      simp only [Expr.uniq] at hu
      have hT : T.ftv.all Ta.contains = true := by
        simp only [Ty.ftvList, List.all_append, Bool.and_eq_true] at hc; exact hc.1.2.1
      have hTs : (Ty.ftvList Ts).all Ta.contains = true := by
        simp only [Ty.ftvList, List.all_append, Bool.and_eq_true] at hc; exact hc.1.2.2
      rw [env.tys hTs, env.ty hT]
      exact RenE.superCall (RenE.comp h1 h2 env hc.1.1 hn.1 ha.1 hb.1 hu.1)
        (RenEs.comp hs1 hs2 env hc.2 hn.2 ha.2 hb.2 hu.2)
  | .field h1, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | field h2 =>
      simp only [Expr.closed, Expr.noShadow] at hc hn
      simp only [NoThis, Expr.vbinders] at ha hb
      simp only [Expr.uniq] at hu
      exact RenE.field (RenE.comp h1 h2 env hc hn ha hb hu)
  | .new (Ts := Ts) hs1, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | new hs2 =>
      simp only [Expr.closed, Bool.and_eq_true, Expr.noShadow] at hc hn
      simp only [NoThis, Expr.vbinders] at ha hb
      simp only [Expr.uniq] at hu
      rw [env.tys hc.1]
      exact RenE.new (RenEs.comp hs1 hs2 env hc.2 hn ha hb hu)
  | .newLocal (Fs := Fs) (Ts := Ts) hs1 hm1, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | newLocal hs2 hm2 =>
      simp only [Expr.closed, Bool.and_eq_true, List.all_append, Expr.noShadow] at hc hn
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
      simp only [Expr.uniq] at hu
      rw [env.tys hc.1.1.2, Funnels.ren_comp (fun X hX => (env.st X (all_contains_iff.mp hc.1.1.1 X hX)).2)]
      exact RenE.newLocal (RenEs.comp hs1 hs2 env hc.1.2 hn.1 ha.1 hb.1 hu.1)
        (RenMs.comp hm1 hm2 env.filt hc.2 hn.2 ha.2 hb.2 hu.2)
  | .ifInst (T := T) (x := x) (y := y) h01 h11 h21, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | ifInst h02 h12 h22 =>
      simp only [Expr.closed, Bool.and_eq_true, Expr.noShadow, Bool.not_eq_true'] at hc hn
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ha hb
      simp only [Expr.uniq] at hu
      have hyS : Not (List.Mem y Sb) := by
        have := hn.1.1.2
        simp at this
        exact this
      rw [env.ty hc.1.1.2]
      exact RenE.ifInst (RenE.comp h01 h02 env hc.1.1.1 hn.1.1.1 ha.1.1.2 hb.1.1.2 hu.1)
        (RenE.comp h11 h12 (env.ifExt (fun e => ha.1.1.1 e.symm) (fun e => hb.1.1.1 e.symm) hyS) hc.1.2 hn.1.2
          ha.1.2 hb.1.2 hu.2.1)
        (RenE.comp h21 h22 env hc.2 hn.2 ha.2 hb.2 hu.2.2)
theorem RenEs.comp {rv1 rt1 as bs} : RenEs rv1 rt1 as bs -> forall {rv2 rt2 cs rv3 rt3 Sa Sb Ta Tb},
    RenEs rv2 rt2 bs cs -> CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb -> Expr.closedList Ta Sa as = true ->
    Expr.noShadowList Tb Sb bs = true -> Not (List.Mem this (Expr.vbindersList as)) ->
    Not (List.Mem this (Expr.vbindersList bs)) -> Expr.uniqList bs -> RenEs rv3 rt3 as cs
  | .nil, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, _, _, _, _, _, _ => by cases h2; exact RenEs.nil
  | .cons h1 hs1, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | cons h2 hs2 =>
      simp only [Expr.closedList, Bool.and_eq_true, Expr.noShadowList] at hc hn
      simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ha hb
      simp only [Expr.uniqList] at hu
      exact RenEs.cons (RenE.comp h1 h2 env hc.1 hn.1 ha.1 hb.1 hu.1)
        (RenEs.comp hs1 hs2 env hc.2 hn.2 ha.2 hb.2 hu.2)
theorem RenM.comp {rv1 rt1 Ma Mb} : RenM rv1 rt1 Ma Mb -> forall {rv2 rt2 Mc rv3 rt3 Sa Sb Ta Tb},
    RenM rv2 rt2 Mb Mc -> CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb -> Ma.closed Ta Sa = true ->
    Mb.noShadow Tb Sb = true -> NoThisM Ma -> NoThisM Mb -> Mb.uniq -> RenM rv3 rt3 Ma Mc
  | .mk (Delta := Da) (T0 := T0) (m := m) (ps := psa) (Xs' := Xs1) (xs' := xs1) hL1 hl1 h1,
      rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | @mk _ _ _ _ _ _ _ _ Xs2 xs2 hL2 hl2 h2 =>
      rw [dom_renBounds hL1] at h2
      rw [names_renParams hl1] at h2
      simp only [Method.closed, Bool.and_eq_true, Method.noShadow] at hc hn
      simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
      simp only [Method.uniq] at hu
      rw [dom_renBounds hL1] at hn hu
      rw [names_renParams hl1] at hn hb hu
      have hla : (psa.map VarDecl.x).length = xs1.length := by simp [hl1]
      have hlb : xs1.length = xs2.length := by rw [hl2]; simp [hl1]
      have hLa : (dom Da).length = Xs1.length := by simp [dom, hL1]
      have hLb : Xs1.length = Xs2.length := by rw [hL2]; simp [hL1]
      have env' := env.methExt hla hlb hu.2.1 hLa hLb hu.1 ha.1 hb.1 hn.1.2 hn.1.1
      have hbody := RenE.comp h1 h2 env' hc.2 hn.2 ha.2 hb.2 hu.2.2
      have hm := RenM.mk (rv := rv3) (rt := rt3) (Delta := Da) (T0 := T0) (m := m) (ps := psa)
        (Xs' := Xs2) (xs' := xs2) (by rw [<- hLb, hL1]) (by rw [<- hlb, hl1]) hbody
      have hty : forall T : Ty, T.ftv.all (Ta ++ dom Da).contains = true ->
          (T.ren ((dom Da).zip Xs1 ++ rt1)).ren (Xs1.zip Xs2 ++ _) = T.ren ((dom Da).zip Xs2 ++ rt3) :=
        fun T hT => env'.ty hT
      have hall := all_contains_iff.mp hc.1
      have hT0 : T0.ftv.all (Ta ++ dom Da).contains = true :=
        all_contains_iff.mpr (fun X hX => hall X (List.mem_append_left _ hX))
      rw [dom_renBounds hL1]
      rw [hty T0 hT0, bounds_comp hL1 (by rw [<- hLb, hL1])
          (fun b hb' => hty b.T (all_contains_iff.mpr (fun X hX => hall X (List.mem_append_right _
            (by rw [List.append_eq, ftvList_append]; exact List.mem_append_left _ (ftvList_map_mem (f := Bound.T) hb' hX)))))),
        params_comp hl1 (by rw [<- hlb, hl1])
          (fun p hp => hty p.T (all_contains_iff.mpr (fun X hX => hall X (List.mem_append_right _
            (by rw [List.append_eq, ftvList_append]; exact List.mem_append_right _ (ftvList_map_mem (f := VarDecl.T) hp hX))))))]
      exact hm
theorem RenMs.comp {rv1 rt1 Mas Mbs} : RenMs rv1 rt1 Mas Mbs -> forall {rv2 rt2 Mcs rv3 rt3 Sa Sb Ta Tb},
    RenMs rv2 rt2 Mbs Mcs -> CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb ->
    Method.closedList Ta Sa Mas = true -> Method.noShadowList Tb Sb Mbs = true ->
    Not (List.Mem this (Method.vbindersList Mas)) -> Not (List.Mem this (Method.vbindersList Mbs)) ->
    Method.uniqList Mbs -> RenMs rv3 rt3 Mas Mcs
  | .nil, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, _, _, _, _, _, _ => by cases h2; exact RenMs.nil
  | .cons h1 hs1, rv2, rt2, c, rv3, rt3, Sa, Sb, Ta, Tb, h2, env, hc, hn, ha, hb, hu => by
    cases h2 with
    | cons h2 hs2 =>
      simp only [Method.closedList, Bool.and_eq_true, Method.noShadowList] at hc hn
      simp only [Method.vbindersList, listMem_iff, List.mem_append, not_or] at ha hb
      simp only [Method.uniqList] at hu
      exact RenMs.cons (RenM.comp h1 h2 env hc.1 hn.1 ha.1 hb.1 hu.1)
        (RenMs.comp hs1 hs2 env hc.2 hn.2 ha.2 hb.2 hu.2)
end

end Funnelling.High