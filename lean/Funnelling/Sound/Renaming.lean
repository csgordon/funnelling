import Funnelling.Sound.Decomposition

open Funnelling.SoundSimp

namespace Funnelling

theorem all_contains_iff {A : Type} [DecidableEq A] {l xs : List A} :
    l.all xs.contains = true <-> forall x, List.Mem x l -> List.Mem x xs := by
  simp [List.all_eq_true]

theorem ftvList_mem {X : TVarName} : forall {Ts : List Ty},
    List.Mem X (Ty.ftvList Ts) <-> exists T, List.Mem T Ts /\ List.Mem X T.ftv
  | [] => by simp [Ty.ftvList]
  | T :: Ts => by
    have ih := @ftvList_mem X Ts
    simp only [listMem_iff] at ih |-
    simp [Ty.ftvList, ih, or_and_right, exists_or]

mutual
theorem Ty.ren_comp {rt1 rt2 rt3 : TRen} : forall {T : Ty},
    (forall X, List.Mem X T.ftv -> rn rt2 (rn rt1 X) = rn rt3 X) -> (T.ren rt1).ren rt2 = T.ren rt3
  | .var X, h => by
    simp only [Ty.ren, TVarName.ren_eq]
    rw [h X (by simp [Ty.ftv])]
  | .cls C Ts, h => by
    simp only [Ty.ren]
    rw [Ty.renList_comp (fun X hX => h X (by simpa [Ty.ftv] using hX))]
theorem Ty.renList_comp {rt1 rt2 rt3 : TRen} : forall {Ts : List Ty},
    (forall X, List.Mem X (Ty.ftvList Ts) -> rn rt2 (rn rt1 X) = rn rt3 X) ->
    Ty.renList rt2 (Ty.renList rt1 Ts) = Ty.renList rt3 Ts
  | [], _ => rfl
  | T :: Ts, h => by
    simp only [Ty.renList]
    rw [Ty.ren_comp (fun X hX => h X (List.mem_append_left _ hX)),
      Ty.renList_comp (fun X hX => h X (List.mem_append_right _ hX))]
end

mutual
theorem Ty.ren_id {rt : TRen} : forall {T : Ty}, (forall X, List.Mem X T.ftv -> rn rt X = X) -> T.ren rt = T
  | .var X, h => by
    simp only [Ty.ren, TVarName.ren_eq]
    rw [h X (by simp [Ty.ftv])]
  | .cls C Ts, h => by
    simp only [Ty.ren]
    rw [Ty.renList_id (fun X hX => h X (by simpa [Ty.ftv] using hX))]
theorem Ty.renList_id {rt : TRen} : forall {Ts : List Ty},
    (forall X, List.Mem X (Ty.ftvList Ts) -> rn rt X = X) -> Ty.renList rt Ts = Ts
  | [], _ => rfl
  | T :: Ts, h => by
    simp only [Ty.renList]
    rw [Ty.ren_id (fun X hX => h X (List.mem_append_left _ hX)),
      Ty.renList_id (fun X hX => h X (List.mem_append_right _ hX))]
end

theorem Ty.renList_eq_map {rt : TRen} : forall {Ts : List Ty}, Ty.renList rt Ts = Ts.map (Ty.ren rt)
  | [] => rfl
  | T :: Ts => by simp [Ty.renList, Ty.renList_eq_map]

theorem Funnel.ren_comp {rt1 rt2 rt3 : TRen} {F : Funnel}
    (h : forall X, List.Mem X (domF [F]) -> rn rt2 (rn rt1 X) = rn rt3 X) :
    (F.ren rt1).ren rt2 = F.ren rt3 := by
  cases F with
  | ground G => rfl
  | funnel X =>
    simp only [Funnel.ren, TVarName.ren_eq]
    rw [h X (by simp [domF])]

theorem Funnel.ren_id {rt : TRen} {F : Funnel}
    (h : forall X, List.Mem X (domF [F]) -> rn rt X = X) : F.ren rt = F := by
  cases F with
  | ground G => rfl
  | funnel X =>
    simp only [Funnel.ren, TVarName.ren_eq]
    rw [h X (by simp [domF])]

theorem domF_cons {F : Funnel} {Fs : List Funnel} : domF (F :: Fs) = domF [F] ++ domF Fs := by cases F <;> simp [domF]

theorem Funnels.ren_comp {rt1 rt2 rt3 : TRen} : forall {Fs : List Funnel},
    (forall X, List.Mem X (domF Fs) -> rn rt2 (rn rt1 X) = rn rt3 X) ->
    (Fs.map (Funnel.ren rt1)).map (Funnel.ren rt2) = Fs.map (Funnel.ren rt3)
  | [], _ => rfl
  | F :: Fs, h => by
    simp only [List.map_cons]
    rw [Funnel.ren_comp (fun X hX => h X (by rw [domF_cons]; exact List.mem_append_left _ hX)),
      Funnels.ren_comp (fun X hX => h X (by rw [domF_cons]; exact List.mem_append_right _ hX))]

theorem Funnels.ren_id {rt : TRen} : forall {Fs : List Funnel},
    (forall X, List.Mem X (domF Fs) -> rn rt X = X) -> Fs.map (Funnel.ren rt) = Fs
  | [], _ => rfl
  | F :: Fs, h => by
    simp only [List.map_cons]
    rw [Funnel.ren_id (fun X hX => h X (by rw [domF_cons]; exact List.mem_append_left _ hX)),
      Funnels.ren_id (fun X hX => h X (by rw [domF_cons]; exact List.mem_append_right _ hX))]

theorem bounds_zip_dom : forall (Delta : Bounds),
    (Delta.zip (dom Delta)).map (fun p => ({ X := p.2, T := p.1.T } : Bound)) = Delta
  | [] => rfl
  | b :: Delta => by
    simp only [dom, List.map_cons, List.zip_cons_cons]
    rw [show List.map Bound.X Delta = dom Delta from rfl, bounds_zip_dom Delta]

theorem params_zip_names : forall (ps : List VarDecl),
    (ps.zip (ps.map VarDecl.x)).map (fun p => ({ T := p.1.T, x := p.2 } : VarDecl)) = ps
  | [] => rfl
  | p :: ps => by
    simp only [List.map_cons, List.zip_cons_cons]
    rw [params_zip_names ps]

abbrev IdRen {A : Type} (r : List (Prod A A)) : Prop := forall p, List.Mem p r -> p.1 = p.2

theorem IdRen.cons {A : Type} {r : List (Prod A A)} {x : A} (h : IdRen r) : IdRen ((x, x) :: r) := by
  intro p hp
  cases hp with
  | head => rfl
  | tail _ hp => exact h p hp

theorem IdRen.zip_append {A : Type} {r : List (Prod A A)} (h : IdRen r) :
    forall (xs : List A), IdRen (xs.zip xs ++ r)
  | [] => h
  | _ :: xs => IdRen.cons (IdRen.zip_append h xs)

theorem Ty.ren_idRen {rt : TRen} (h : IdRen rt) (T : Ty) : T.ren rt = T :=
  Ty.ren_id (fun X _ => rn_id h X)

theorem Ty.renList_idRen {rt : TRen} (h : IdRen rt) (Ts : List Ty) : Ty.renList rt Ts = Ts :=
  Ty.renList_id (fun X _ => rn_id h X)

mutual
theorem RenE.refl {rv : VRen} {rt : TRen} (hv : IdRen rv) (ht : IdRen rt) : forall (e : Expr), RenE rv rt e e
  | .var x => by
    have := RenE.var (rv := rv) (rt := rt) (x := x)
    rwa [VarName.ren_eq, rn_id hv] at this
  | .call e Ts m es => by
    have := RenE.call (m := m) (Ts := Ts) (RenE.refl hv ht e) (RenEs.refl hv ht es)
    rwa [Ty.renList_idRen ht] at this
  | .superCall e T Ts m es => by
    have := RenE.superCall (m := m) (T := T) (Ts := Ts) (RenE.refl hv ht e) (RenEs.refl hv ht es)
    rwa [Ty.renList_idRen ht, Ty.ren_idRen ht] at this
  | .field e f => RenE.field (RenE.refl hv ht e)
  | .new C Ts es => by
    have := RenE.new (C := C) (Ts := Ts) (RenEs.refl hv ht es)
    rwa [Ty.renList_idRen ht] at this
  | .newLocal C Fs C' Ts es Ms => by
    have := RenE.newLocal (C := C) (Fs := Fs) (C' := C') (Ts := Ts) (RenEs.refl hv ht es) (RenMs.refl hv ht Ms)
    rwa [Ty.renList_idRen ht, Funnels.ren_id (fun X _ => rn_id ht X)] at this
  | .ifInst e0 T x e1 e2 => by
    have := RenE.ifInst (T := T) (RenE.refl hv ht e0) (RenE.refl (IdRen.cons (x := x) hv) ht e1) (RenE.refl hv ht e2)
    rwa [Ty.ren_idRen ht] at this
theorem RenEs.refl {rv : VRen} {rt : TRen} (hv : IdRen rv) (ht : IdRen rt) : forall (es : List Expr), RenEs rv rt es es
  | [] => RenEs.nil
  | e :: es => RenEs.cons (RenE.refl hv ht e) (RenEs.refl hv ht es)
theorem RenM.refl {rv : VRen} {rt : TRen} (hv : IdRen rv) (ht : IdRen rt) : forall (M : Method), RenM rv rt M M
  | .mk Delta T0 m ps e => by
    have h := RenM.mk (rv := rv) (rt := rt) (Delta := Delta) (T0 := T0) (m := m) (ps := ps)
      (Xs' := dom Delta) (xs' := ps.map VarDecl.x) (by simp [dom]) (by simp)
      (RenE.refl (IdRen.zip_append hv _) (IdRen.zip_append ht _) e)
    have ht' := IdRen.zip_append ht (dom Delta)
    simp only [Ty.ren_idRen ht'] at h
    rwa [bounds_zip_dom, params_zip_names] at h
theorem RenMs.refl {rv : VRen} {rt : TRen} (hv : IdRen rv) (ht : IdRen rt) : forall (Ms : List Method), RenMs rv rt Ms Ms
  | [] => RenMs.nil
  | M :: Ms => RenMs.cons (RenM.refl hv ht M) (RenMs.refl hv ht Ms)
end

theorem Fresh.refl (e : Expr) : Fresh e e :=
  And.intro (RenE.refl (by intro p hp; cases hp) (by intro p hp; cases hp) e)
    (RenE.refl (by intro p hp; cases hp) (by intro p hp; cases hp) e)

mutual
def Expr.uniq : Expr -> Prop
  | .var _ => True
  | .call e _ _ es => e.uniq /\ Expr.uniqList es
  | .superCall e _ _ _ es => e.uniq /\ Expr.uniqList es
  | .field e _ => e.uniq
  | .new _ _ es => Expr.uniqList es
  | .newLocal _ _ _ _ es Ms => Expr.uniqList es /\ Method.uniqList Ms
  | .ifInst e0 _ _ e1 e2 => e0.uniq /\ e1.uniq /\ e2.uniq
def Expr.uniqList : List Expr -> Prop
  | [] => True
  | e :: es => e.uniq /\ Expr.uniqList es
def Method.uniq : Method -> Prop
  | .mk Delta _ _ ps e => (dom Delta).Nodup /\ (ps.map VarDecl.x).Nodup /\ e.uniq
def Method.uniqList : List Method -> Prop
  | [] => True
  | M :: Ms => M.uniq /\ Method.uniqList Ms
end

abbrev NoThis (e : Expr) : Prop := Not (List.Mem this e.vbinders)

abbrev NoThisM (M : Method) : Prop := Not (List.Mem this M.vbinders)

theorem rn_this {rv : VRen} (h : forall p, List.Mem p rv -> Not (p.1 = this)) : rn rv this = this := by
  simp only [rn]
  rw [lookup_none (fun p hp e => h p hp e)]
  rfl

theorem rn_ne_this {rv : VRen} (h : forall p, List.Mem p rv -> Not (p.2 = this)) {w : VarName}
    (hw : Not (w = this)) : Not (rn rv w = this) := by
  simp only [rn]
  cases hl : List.lookup w rv with
  | none => exact hw
  | some y => exact h (w, y) (lookup_mem hl)

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

theorem rn_zip_self {A : Type} [DecidableEq A] : forall {xs : List A} {r : List (Prod A A)} {w : A},
    List.Mem w xs -> rn (xs.zip xs ++ r) w = w
  | [], _, _, h => by cases h
  | a :: xs, r, w, h => by
    simp only [List.zip_cons_cons, List.cons_append]
    by_cases e : w = a
    . subst e; exact rn_cons_eq
    . rw [rn_cons_ne e]
      cases h with
      | head => exact absurd rfl e
      | tail _ h => exact rn_zip_self h

theorem rn_zip_self_or {A : Type} [DecidableEq A] {xs : List A} {r : List (Prod A A)} {w : A}
    (h : Not (List.Mem w xs) -> rn r w = w) : rn (xs.zip xs ++ r) w = w := by
  by_cases hm : List.Mem w xs
  . exact rn_zip_self hm
  . rw [rn_zip_not_mem hm]; exact h hm

theorem bounds_zip_dom_ren {rt : TRen} : forall {Delta : Bounds},
    (forall b, List.Mem b Delta -> b.T.ren rt = b.T) ->
    (Delta.zip (dom Delta)).map (fun p => ({ X := p.2, T := p.1.T.ren rt } : Bound)) = Delta
  | [], _ => rfl
  | b :: Delta, h => by
    simp only [dom, List.map_cons, List.zip_cons_cons]
    rw [h b (List.Mem.head _),
      show List.map Bound.X Delta = dom Delta from rfl,
      bounds_zip_dom_ren (fun b' hb' => h b' (List.Mem.tail _ hb'))]

theorem params_zip_names_ren {rt : TRen} : forall {ps : List VarDecl},
    (forall p, List.Mem p ps -> p.T.ren rt = p.T) ->
    (ps.zip (ps.map VarDecl.x)).map (fun p => ({ T := p.1.T.ren rt, x := p.2 } : VarDecl)) = ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [List.map_cons, List.zip_cons_cons]
    rw [h p (List.Mem.head _), params_zip_names_ren (fun p' hp' => h p' (List.Mem.tail _ hp'))]

mutual
theorem RenE.reflS {rv : VRen} {rt : TRen} : forall {e : Expr} {Ts : List TVarName} {xs : List VarName},
    e.closed Ts xs = true -> (forall w, (List.Mem w xs \/ w = this) -> rn rv w = w) ->
    (forall X, List.Mem X Ts -> rn rt X = X) -> RenE rv rt e e
  | .var x, Ts, xs, hc, hv, _ => by
    simp only [Expr.closed] at hc
    have hx : List.Mem x xs := by simpa using hc
    have := RenE.var (rv := rv) (rt := rt) (x := x)
    rwa [VarName.ren_eq, hv x (Or.inl hx)] at this
  | .call e Ts' m es, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have := RenE.call (m := m) (Ts := Ts') (RenE.reflS hc.1.1 hv ht) (RenEs.reflS hc.2 hv ht)
    rwa [Ty.renList_id (fun X hX => ht X (all_contains_iff.mp hc.1.2 X hX))] at this
  | .superCall e T Ts' m es, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have h2 := all_contains_iff.mp hc.1.2
    have := RenE.superCall (m := m) (T := T) (Ts := Ts') (RenE.reflS hc.1.1 hv ht) (RenEs.reflS hc.2 hv ht)
    rwa [Ty.renList_id (fun X hX => ht X (h2 X (List.mem_append_right _ hX))),
      Ty.ren_id (fun X hX => ht X (h2 X (List.mem_append_left _ hX)))] at this
  | .field e f, Ts, xs, hc, hv, ht => RenE.field (RenE.reflS hc hv ht)
  | .new C Ts' es, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have := RenE.new (C := C) (Ts := Ts') (RenEs.reflS hc.2 hv ht)
    rwa [Ty.renList_id (fun X hX => ht X (all_contains_iff.mp hc.1 X hX))] at this
  | .newLocal C Fs C' Ts' es Ms, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have h1 := all_contains_iff.mp hc.1.1
    have := RenE.newLocal (C := C) (Fs := Fs) (C' := C') (Ts := Ts') (RenEs.reflS hc.1.2 hv ht)
      (RenMs.reflS hc.2 hv ht)
    rwa [Ty.renList_id (fun X hX => ht X (h1 X (List.mem_append_right _ hX))),
      Funnels.ren_id (fun X hX => ht X (h1 X (List.mem_append_left _ hX)))] at this
  | .ifInst e0 T x e1 e2, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have hv' : forall w, (List.Mem w (x :: xs) \/ w = this) -> rn ((x, x) :: rv) w = w := by
      intro w hw
      by_cases e : w = x
      . subst e; exact rn_cons_eq
      . rw [rn_cons_ne e]
        apply hv
        rcases hw with hw | hw
        . simp_all
        . exact Or.inr hw
    have := RenE.ifInst (T := T) (y := x) (RenE.reflS hc.1.1.1 hv ht) (RenE.reflS hc.1.2 hv' ht)
      (RenE.reflS hc.2 hv ht)
    rwa [Ty.ren_id (fun X hX => ht X (all_contains_iff.mp hc.1.1.2 X hX))] at this
theorem RenEs.reflS {rv : VRen} {rt : TRen} : forall {es : List Expr} {Ts : List TVarName} {xs : List VarName},
    Expr.closedList Ts xs es = true -> (forall w, (List.Mem w xs \/ w = this) -> rn rv w = w) ->
    (forall X, List.Mem X Ts -> rn rt X = X) -> RenEs rv rt es es
  | [], _, _, _, _, _ => RenEs.nil
  | e :: es, Ts, xs, hc, hv, ht => by
    simp only [Expr.closedList, Bool.and_eq_true] at hc
    exact RenEs.cons (RenE.reflS hc.1 hv ht) (RenEs.reflS hc.2 hv ht)
theorem RenM.reflS {rv : VRen} {rt : TRen} : forall {M : Method} {Ts : List TVarName} {xs : List VarName},
    M.closed Ts xs = true -> (forall w, (List.Mem w xs \/ w = this) -> rn rv w = w) ->
    (forall X, List.Mem X Ts -> rn rt X = X) -> RenM rv rt M M
  | .mk Delta T0 m ps e, Ts, xs, hc, hv, ht => by
    simp only [Method.closed, Bool.and_eq_true] at hc
    have hall := all_contains_iff.mp hc.1
    have ht' : forall X, List.Mem X (Ts ++ dom Delta) -> rn ((dom Delta).zip (dom Delta) ++ rt) X = X := by
      intro X hX
      apply rn_zip_self_or
      intro hn
      exact (List.mem_append.mp hX).elim (ht X) (fun hX => absurd hX hn)
    have hv' : forall w, (List.Mem w (this :: xs ++ ps.map VarDecl.x) \/ w = this) ->
        rn ((ps.map VarDecl.x).zip (ps.map VarDecl.x) ++ rv) w = w := by
      intro w hw
      apply rn_zip_self_or
      intro hn
      apply hv
      simp only [listMem_iff, List.mem_append, List.mem_cons] at hw hn
      rcases hw with ((hw | hw) | hw) | hw
      . exact Or.inr hw
      . exact Or.inl hw
      . exact absurd hw hn
      . exact Or.inr hw
    have h := RenM.mk (rv := rv) (rt := rt) (Delta := Delta) (T0 := T0) (m := m) (ps := ps)
      (Xs' := dom Delta) (xs' := ps.map VarDecl.x) (by simp [dom]) (by simp)
      (RenE.reflS hc.2 hv' ht')
    have hty : forall T : Ty, (forall X, List.Mem X T.ftv -> List.Mem X (Ty.ftvList (T0 :: cod Delta ++ ps.map VarDecl.T))) ->
        T.ren ((dom Delta).zip (dom Delta) ++ rt) = T :=
      fun T hT => Ty.ren_id (fun X hX => ht' X (hall X (hT X hX)))
    rw [hty T0 (fun X hX => by simp only [List.cons_append]; exact List.mem_append_left _ hX),
      bounds_zip_dom_ren (fun b hb => hty b.T (fun X hX => by
        simp only [List.cons_append, Ty.ftvList]
        exact List.mem_append_right _ (by rw [ftvList_append]; exact List.mem_append_left _ (ftvList_map_mem (f := Bound.T) hb hX)))),
      params_zip_names_ren (fun p hp => hty p.T (fun X hX => by
        simp only [List.cons_append, Ty.ftvList]
        exact List.mem_append_right _ (by rw [ftvList_append]; exact List.mem_append_right _ (ftvList_map_mem (f := VarDecl.T) hp hX))))] at h
    exact h
theorem RenMs.reflS {rv : VRen} {rt : TRen} : forall {Ms : List Method} {Ts : List TVarName} {xs : List VarName},
    Method.closedList Ts xs Ms = true -> (forall w, (List.Mem w xs \/ w = this) -> rn rv w = w) ->
    (forall X, List.Mem X Ts -> rn rt X = X) -> RenMs rv rt Ms Ms
  | [], _, _, _, _, _ => RenMs.nil
  | M :: Ms, Ts, xs, hc, hv, ht => by
    simp only [Method.closedList, Bool.and_eq_true] at hc
    exact RenMs.cons (RenM.reflS hc.1 hv ht) (RenMs.reflS hc.2 hv ht)
end

theorem RenE.value {rv : VRen} {rt : TRen} {v : Value} (hc : v.expr.closed [] [] = true)
    (ht : rn rv this = this) : RenE rv rt v.expr v.expr :=
  RenE.reflS hc (fun w hw => by
    rcases hw with hw | hw
    . cases hw
    . subst hw; exact ht) (fun X hX => by cases hX)

end Funnelling
