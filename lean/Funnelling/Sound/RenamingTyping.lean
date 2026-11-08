import Funnelling.Sound.VarSubstitution

open Funnelling.SoundSimp

namespace Funnelling

abbrev tS (rt : TRen) : TSubst := rt.map fun p => (p.1, Ty.var p.2)

theorem lookup_tS {X : TVarName} : forall {rt : TRen}, (Ty.var X).subst (tS rt) = Ty.var (rn rt X)
  | [] => rfl
  | (a, b) :: rt => by
    by_cases e : X = a
    . subst e
      simp only [tS, List.map_cons, Ty.subst]
      rw [lookup_cons_eq, rn_cons_eq]
      rfl
    . have ih := @lookup_tS X rt
      simp only [tS, List.map_cons, Ty.subst]
      rw [lookup_cons_ne e, rn_cons_ne e]
      exact ih

mutual
theorem Ty.ren_subst {rt : TRen} : forall (T : Ty), T.ren rt = T.subst (tS rt)
  | .var X => by
    rw [lookup_tS]
    rfl
  | .cls C Ts => by
    simp only [Ty.ren, Ty.subst]
    rw [Ty.renList_subst Ts]
theorem Ty.renList_subst {rt : TRen} : forall (Ts : List Ty), Ty.renList rt Ts = Ty.substList (tS rt) Ts
  | [] => rfl
  | T :: Ts => by
    simp only [Ty.renList, Ty.substList]
    rw [Ty.ren_subst T, Ty.renList_subst Ts]
end

mutual
theorem Ty.ftv_ren {rt : TRen} : forall (T : Ty), (T.ren rt).ftv = T.ftv.map (rn rt)
  | .var _ => rfl
  | .cls _ Ts => Ty.ftvList_ren Ts
theorem Ty.ftvList_ren {rt : TRen} : forall (Ts : List Ty), Ty.ftvList (Ty.renList rt Ts) = (Ty.ftvList Ts).map (rn rt)
  | [] => rfl
  | T :: Ts => by
    simp only [Ty.renList, Ty.ftvList, List.map_append]
    rw [Ty.ftv_ren T, Ty.ftvList_ren Ts]
end

theorem Ty.ren_congr {r1 r2 : TRen} {T : Ty} (h : forall X, List.Mem X T.ftv -> rn r1 X = rn r2 X) :
    T.ren r1 = T.ren r2 := by
  have := Ty.ren_comp (rt1 := []) (rt2 := r1) (rt3 := r2) (T := T) (fun X hX => by rw [rn_nil]; exact h X hX)
  rwa [Ty.ren_idRen (rt := []) (fun p hp => by cases hp)] at this

theorem renList_length {rt : TRen} {Ts : List Ty} : (Ty.renList rt Ts).length = Ts.length := by
  rw [Ty.renList_eq_map]; simp

theorem renList_append {rt : TRen} {Ts Us : List Ty} :
    Ty.renList rt (Ts ++ Us) = Ty.renList rt Ts ++ Ty.renList rt Us := by
  simp [Ty.renList_eq_map]

theorem renList_bind {rt : TRen} {Dl : Bounds} {Us Ts : List Ty} (hl : Us.length = Dl.length)
    (hT : forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X (dom Dl)) :
    Ty.renList rt (Ty.substList (bind Dl Us) Ts) = Ty.substList (bind Dl (Ty.renList rt Us)) Ts := by
  rw [Ty.renList_subst, Ty.renList_subst]
  exact substList_bind_comp hl hT

theorem ren_bind {rt : TRen} {Dl : Bounds} {Us : List Ty} {T : Ty} (hl : Us.length = Dl.length)
    (hT : forall X, List.Mem X T.ftv -> List.Mem X (dom Dl)) :
    (T.subst (bind Dl Us)).ren rt = T.subst (bind Dl (Ty.renList rt Us)) := by
  rw [Ty.ren_subst, Ty.renList_subst]
  exact subst_bind_comp hl hT

abbrev BRen (rt : TRen) (Delta Delta' : Bounds) : Prop :=
  forall b, List.Mem b Delta -> List.Mem { X := rn rt b.X, T := b.T.ren rt } Delta'

theorem BRen.ctx {rt : TRen} {Delta Delta' : Bounds} (h : BRen rt Delta Delta') : RenCtx Delta Delta' (tS rt) :=
  fun b hb => Exists.intro (rn rt b.X) (And.intro lookup_tS (by rw [<- Ty.ren_subst]; exact h b hb))

theorem Sub.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {T1 T2 : Ty} (h : Sub d Delta T1 T2) : Sub d Delta' (T1.ren rt) (T2.ren rt) := by
  rw [Ty.ren_subst, Ty.ren_subst]; exact Sub.subst hd hb.ctx.sub h

theorem Kind.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {T : Ty} (h : Kind d Delta T) : Kind d Delta' (T.ren rt) := by
  rw [Ty.ren_subst]; exact Kind.subst hd hb.ctx.sub hb.ctx.kind h

theorem Cast.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {T1 T2 : Ty} (h : Cast d Delta T1 T2) : Cast d Delta' (T1.ren rt) (T2.ren rt) := by
  rw [Ty.ren_subst, Ty.ren_subst]; exact Cast.ren hd hb.ctx h

theorem SubSeq.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {Ts Us : List Ty} (h : SubSeq d Delta Ts Us) : SubSeq d Delta' (Ty.renList rt Ts) (Ty.renList rt Us) := by
  rw [Ty.renList_subst, Ty.renList_subst]; exact SubSeq.subst hd hb.ctx.sub h

theorem KindSeq.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {Ts : List Ty} (h : KindSeq d Delta Ts) : KindSeq d Delta' (Ty.renList rt Ts) := by
  intro T hT
  rw [Ty.renList_eq_map] at hT
  rcases List.mem_map.mp hT with ⟨U, hU⟩; rw [<- hU.2]; exact Kind.renT hd hb (h U hU.1)

theorem Scope.renT {d : Decls} {rt : TRen} {C : ClassName} {Ts : List Ty} {Delta0 : Bounds} {Ts0 : List Ty}
    (h : Scope d (.cls C Ts) Delta0 Ts0) : Scope d (.cls C (Ty.renList rt Ts)) Delta0 (Ty.renList rt Ts0) := by
  have := h.subst (s := tS rt)
  rw [Ty.renList_subst, Ty.renList_subst]
  exact this

theorem abs_ren {rt : TRen} : forall {Fs : List Funnel}, abs (Fs.map (Funnel.ren rt)) = Ty.renList rt (abs Fs)
  | [] => rfl
  | F :: Fs => by
    simp only [abs, List.map_cons, Ty.renList] at |-
    rw [show List.map Funnel.abs (List.map (Funnel.ren rt) Fs) = abs (Fs.map (Funnel.ren rt)) from rfl, abs_ren]
    cases F with
    | ground G => simp only [Funnel.ren, Funnel.abs]; rw [GTy.ren_ty]; rfl
    | funnel X => rfl

theorem Pairing.renT {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta') {Fs : List Funnel}
    {Ts : List Ty} {Dp : Bounds} {Tp : List Ty} (h : Pairing Delta Fs Ts Dp Tp) :
    Pairing Delta' (Fs.map (Funnel.ren rt)) (Ty.renList rt Ts)
      (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) (Ty.renList rt Tp) := by
  induction h with
  | nil => exact Pairing.nil
  | funnel hm _ ih => exact Pairing.funnel (hb _ hm) ih
  | @ground G Fs Ts Delta0 Ts0 _ ih =>
    simp only [List.map_cons, Funnel.ren, Ty.renList]
    rw [GTy.ren_ty]
    exact Pairing.ground ih

theorem Gamma.lookup_append_left {g1 g2 : Gamma} {x : VarName} {U : Ty} (h : g1.lookup x = some U) :
    (g1 ++ g2).lookup x = some U := by
  simp only [Gamma.lookup, List.find?_append] at h |-
  cases hf : List.find? (fun d => d.x == x) g1 with
  | none => rw [hf] at h; cases h
  | some y => rw [hf] at h; simpa using h

theorem Gamma.lookup_append_right {g1 g2 : Gamma} {x : VarName} (h : g1.lookup x = none) :
    (g1 ++ g2).lookup x = g2.lookup x := by
  simp only [Gamma.lookup, List.find?_append] at h |-
  cases hf : List.find? (fun d => d.x == x) g1 with
  | none => simp
  | some y => rw [hf] at h; cases h

theorem Gamma.lookup_none {g : Gamma} {x : VarName} (h : Not (List.Mem x (gdom g))) : g.lookup x = none := by
  cases hl : g.lookup x with
  | none => rfl
  | some U => exact absurd (List.mem_map_of_mem (f := VarDecl.x) (lookup_mem_g hl)) h

theorem Gamma.lookup_single {T : Ty} {x : VarName} : Gamma.lookup [{ T := T, x := x }] x = some T := by
  simp [Gamma.lookup]

theorem Gamma.lookup_single_ne {T : Ty} {x z : VarName} (h : Not (z = x)) :
    Gamma.lookup [{ T := T, x := x }] z = none :=
  Gamma.lookup_none (by simpa [gdom] using h)

theorem Gamma.lookup_filter_of {p : VarDecl -> Bool} : forall {g : Gamma} {x : VarName} {U : Ty},
    Gamma.lookup g x = some U -> p { T := U, x := x } = true -> Gamma.lookup (g.filter p) x = some U
  | [], _, _, h, _ => by simp [Gamma.lookup] at h
  | y :: g, x, U, h, hp => by
    by_cases e : y.x = x
    . have hb : (y.x == x) = true := by simp [e]
      simp only [Gamma.lookup, List.find?_cons, hb, Option.map_some, Option.some.injEq] at h
      have ey : y = { T := U, x := x } := by cases y; simp_all
      subst ey
      rw [List.filter_cons_of_pos hp]
      exact Gamma.lookup_append_left (g2 := List.filter p g) Gamma.lookup_single
    . have hb : (y.x == x) = false := by simp [e]
      have h' : Gamma.lookup g x = some U := by simpa only [Gamma.lookup, List.find?_cons, hb] using h
      have ih := Gamma.lookup_filter_of h' hp
      by_cases hpy : p y = true
      . rw [List.filter_cons_of_pos hpy]
        simp only [Gamma.lookup, List.find?_cons, hb]
        exact ih
      . simp_all

theorem Gamma.lookup_of_filter {p : VarDecl -> Bool} {g : Gamma} {x : VarName} {U : Ty} (hn : (gdom g).Nodup)
    (h : Gamma.lookup (g.filter p) x = some U) : Gamma.lookup g x = some U /\ p { T := U, x := x } = true := by
  have hm := List.mem_filter.mp (lookup_mem_g h)
  exact And.intro (lookup_of_mem_g hn hm.1) hm.2

theorem RenEs.split {rv : VRen} {rt : TRen} : forall {es1 es2 es' : List Expr}, RenEs rv rt (es1 ++ es2) es' ->
    exists a b, es' = a ++ b /\ RenEs rv rt es1 a /\ RenEs rv rt es2 b
  | [], _, es', h => Exists.intro [] (Exists.intro es' (And.intro rfl (And.intro RenEs.nil h)))
  | e :: es1, es2, es', h => by
    rw [List.cons_append] at h
    cases h with
    | cons h1 h2 =>
      rcases RenEs.split h2 with ⟨a, h⟩
      rcases h with ⟨b, h⟩
      rw [h.1]
      exact Exists.intro (_ :: a) (Exists.intro b (And.intro rfl (And.intro (RenEs.cons h1 h.2.1) h.2.2)))

theorem RenMs.mem_inv {rv : VRen} {rt : TRen} {M' : Method} : forall {Ms Ms' : List Method}, RenMs rv rt Ms Ms' ->
    List.Mem M' Ms' -> exists M, List.Mem M Ms /\ RenM rv rt M M'
  | _, _, .nil, h => by cases h
  | _, _, .cons h1 h2, h => by
    cases h with
    | head => exact Exists.intro _ (And.intro (List.Mem.head _) h1)
    | tail _ h =>
      rcases RenMs.mem_inv h2 h with ⟨M, hM⟩; exact Exists.intro M (And.intro (List.Mem.tail _ hM.1) hM.2)

theorem RenM.name {rv : VRen} {rt : TRen} {M M' : Method} (h : RenM rv rt M M') : M'.name = M.name := by cases h; rfl

theorem RenMs.names {rv : VRen} {rt : TRen} : forall {Ms Ms' : List Method}, RenMs rv rt Ms Ms' ->
    Ms'.map Method.name = Ms.map Method.name
  | _, _, .nil => rfl
  | _, _, .cons h1 h2 => by simp only [List.map_cons]; rw [h1.name, RenMs.names h2]

theorem dom_sub1 {A B : Bounds} (h : Sub1 A B) : Sub1 (dom A) (dom B) := by
  intro X hX
  simp only [dom] at hX |-
  rcases List.mem_map.mp hX with ⟨b, hb⟩; rw [<- hb.2]; exact List.mem_map_of_mem (h b hb.1)

theorem field_closed {d : Decls} (hok : DeclsOk d) {D : Dec} {T : Ty} {f : FieldName} (hD : Declared d (.dec D))
    (hm : List.Mem { T := T, f := f } D.Ss) : forall X, List.Mem X T.ftv -> List.Mem X (dom D.bounds) :=
  Kind.ftv ((hok D hD.dec_mem).2.1 T (List.Mem.tail _ (List.mem_map_of_mem (f := Slot.T) hm)))

theorem slots_closed {d : Decls} (hok : DeclsOk d) {D : Dec} (hD : Declared d (.dec D)) :
    forall X, List.Mem X (Ty.ftvList (D.Ss.map Slot.T)) -> List.Mem X (dom D.bounds) := by
  intro X hX
  rcases Ty.mem_ftvList.mp hX with ⟨T, hT⟩; exact Kind.ftv ((hok D hD.dec_mem).2.1 T (List.Mem.tail _ hT.1)) X hT.2

theorem methodIn_closed {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {C0 : ClassName} {Ts0 : List Ty}
    {Delta0 : Bounds} {Ts2 : List Ty} {Delta1 : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl} {body : Expr}
    (hs : Scope d (.cls C0 Ts0) Delta0 Ts2) (hm : MethodIn d (.mk Delta1 T0 m ps body) C0) :
    (forall X, List.Mem X (Ty.ftvList (T0 :: ps.map VarDecl.T)) -> List.Mem X (dom (Delta0 ++ Delta1))) /\
      (forall X, List.Mem X (Ty.ftvList (cod Delta1)) -> List.Mem X (dom (Delta0 ++ Delta1))) := by
  rcases scopeFacts hwf hok hs with ⟨k, hk⟩
  rcases hm with ⟨k', hk'⟩
  have hname : k.name = k'.name := by
    rcases hk.2.1 with ⟨Us, hUs⟩; simp only [Ty.cls.injEq] at hUs; rw [<- hUs.1, hk'.2.1]
  have ek := Declared.unique hwf hk.1 hk'.1 hname
  subst ek
  rcases hk.2.2.meths _ hk'.2.2 with ⟨gamma, hmo⟩
  have hmi := methodOk_inv hmo
  refine And.intro ?_ ?_
  . intro X hX
    rcases Ty.mem_ftvList.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.2.1 T hT.1) X hT.2
  . intro X hX
    rcases Ty.mem_ftvList.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.1 T hT.1) X hT.2

theorem Method.noShadow_dom {Xs : List TVarName} {xs : List VarName} {M : Method} (h : M.noShadow Xs xs = true) :
    forall X, List.Mem X (dom M.bounds) -> Not (List.Mem X Xs) := by
  cases M with
  | mk Dm T0 m ps e =>
    simp only [Method.noShadow, Bool.and_eq_true] at h
    intro X hX
    exact not_mem_of_all_not_contains h.1.1 hX

structure REnv (rv : VRen) (rt : TRen) (Delta Delta' : Bounds) (gamma gamma' : Gamma) (Xs : List TVarName)
    (xs xs' : List VarName) : Prop where
  bD : BRen rt Delta Delta'
  dX : forall X, List.Mem X (dom Delta) -> List.Mem X Xs
  dT : forall b, List.Mem b Delta -> forall X, List.Mem X b.T.ftv -> List.Mem X Xs
  g : forall x U, gamma.lookup x = some U -> gamma'.lookup (rn rv x) = some (U.ren rt)
  gT : forall y, List.Mem y gamma -> forall X, List.Mem X y.T.ftv -> List.Mem X Xs
  gN : (gdom gamma).Nodup
  gx : Sub1 (gdom gamma) xs
  gx' : Sub1 (gdom gamma') xs'
  kv : forall p, List.Mem p rv -> Not (p.1 = this) /\ Not (p.2 = this)

theorem REnv.ext {rv : VRen} {rt : TRen} {Delta Delta' : Bounds} {gamma gamma' : Gamma} {Xs : List TVarName}
    {xs xs' : List VarName} (env : REnv rv rt Delta Delta' gamma gamma' Xs xs xs') {T : Ty} {x y : VarName}
    (hx : Not (List.Mem x xs)) (hy : Not (List.Mem y xs')) (hT : forall X, List.Mem X T.ftv -> List.Mem X Xs)
    (hxt : Not (x = this)) (hyt : Not (y = this)) :
    REnv ((x, y) :: rv) rt Delta Delta' (gamma ++ [{ T := T, x := x }]) (gamma' ++ [{ T := T.ren rt, x := y }]) Xs
      (x :: xs) (y :: xs') where
  bD := env.bD
  dX := env.dX
  dT := env.dT
  g := by
    intro z U hl
    by_cases hz : z = x
    . subst hz
      have h0 : gamma.lookup z = none := Gamma.lookup_none (fun h => hx (env.gx _ h))
      rw [Gamma.lookup_append_right h0, Gamma.lookup_single] at hl
      cases hl
      rw [rn_cons_eq, Gamma.lookup_append_right (Gamma.lookup_none (fun h => hy (env.gx' _ h)))]
      exact Gamma.lookup_single
    . cases hg : gamma.lookup z with
      | none =>
        rw [Gamma.lookup_append_right hg, Gamma.lookup_single_ne hz] at hl
        cases hl
      | some U0 =>
        rw [Gamma.lookup_append_left hg] at hl
        cases hl
        rw [rn_cons_ne hz]
        exact Gamma.lookup_append_left (env.g z _ hg)
  gT := by
    intro w hw
    simp only [listMem_iff, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | hw
    . exact env.gT w hw
    . rw [hw]; exact hT
  gN := by rw [gdom_append_single]; exact nodup_snoc env.gN (fun h => hx (env.gx _ h))
  gx := scope_snoc env.gx
  gx' := scope_snoc env.gx'
  kv := by
    intro p hp
    cases hp with
    | head => exact And.intro hxt hyt
    | tail _ hp => exact env.kv p hp

theorem REnv.meth {rv : VRen} {rt : TRen} {Delta Delta' : Bounds} {gamma gamma' : Gamma} {Xs : List TVarName}
    {xs xs' : List VarName} (env : REnv rv rt Delta Delta' gamma gamma' Xs (this :: xs) (this :: xs'))
    {Dm : Bounds} {ps : List VarDecl} {Ys : List TVarName} {ys : List VarName}
    (hL : Ys.length = Dm.length) (hl : ys.length = ps.length)
    (hdis : forall X, List.Mem X (dom Dm) -> Not (List.Mem X Xs))
    (hpx : (ps.map VarDecl.x).all (fun x => !(xs.contains x)) = true)
    (hpt : Not (List.Mem this (ps.map VarDecl.x)))
    (hyx : forall x, List.Mem x ys -> Not (List.Mem x xs'))
    (hyt : Not (List.Mem this ys))
    (hnd : (dom Dm).Nodup) (hnp : (ps.map VarDecl.x).Nodup) (hny : ys.Nodup)
    (hc1 : forall b, List.Mem b Dm -> forall X, List.Mem X b.T.ftv -> List.Mem X (Xs ++ dom Dm))
    (hc2 : forall p, List.Mem p ps -> forall X, List.Mem X p.T.ftv -> List.Mem X (Xs ++ dom Dm)) :
    REnv ((ps.map VarDecl.x).zip ys ++ rv) ((dom Dm).zip Ys ++ rt) (Delta ++ Dm)
      (Delta' ++ (Dm.zip Ys).map fun p => ({ X := p.2, T := p.1.T.ren ((dom Dm).zip Ys ++ rt) } : Bound))
      (gamma ++ ps)
      (gamma' ++ (ps.zip ys).map fun p => ({ T := p.1.T.ren ((dom Dm).zip Ys ++ rt), x := p.2 } : VarDecl))
      (Xs ++ dom Dm) (this :: xs ++ ps.map VarDecl.x) (this :: xs' ++ ys) where
  bD := by
    intro b hb
    simp only [listMem_iff, List.mem_append] at hb |-
    rcases hb with hb | hb
    . left
      have hbX : Not (List.Mem b.X (dom Dm)) := fun h => hdis b.X h (env.dX b.X (List.mem_map_of_mem (f := Bound.X) hb))
      rw [rn_zip_not_mem hbX, Ty.ren_congr (r2 := rt) (fun X hX => rn_zip_not_mem (fun h => hdis X h (env.dT b hb X hX)))]
      exact env.bD b hb
    . right
      rcases mem_zip_fst hL.symm hb with ⟨Y, hY⟩
      have hY2 : List.Mem (b.X, Y) ((dom Dm).zip Ys) := by
        simp only [dom]
        rw [List.zip_map_left]
        exact List.mem_map_of_mem (f := Prod.map Bound.X id) hY
      rw [rn_zip_pair hnd hY2]
      exact List.mem_map_of_mem (f := fun p => ({ X := p.2, T := p.1.T.ren ((dom Dm).zip Ys ++ rt) } : Bound)) hY
  dX := by
    intro X hX
    rw [dom_append] at hX
    simp only [listMem_iff, List.mem_append] at hX |-
    rcases hX with hX | hX
    . exact Or.inl (env.dX X hX)
    . exact Or.inr hX
  dT := by
    intro b hb X hX
    exact (List.mem_append.mp hb).elim (fun hb => List.mem_append_left _ (env.dT b hb X hX)) (fun hb => hc1 b hb X hX)
  g := by
    intro z U hlk
    cases hg : Gamma.lookup gamma z with
    | some U0 =>
      rw [Gamma.lookup_append_left hg] at hlk
      cases hlk
      have hz : Not (List.Mem z (ps.map VarDecl.x)) := by
        intro hm
        have := env.gx z (List.mem_map_of_mem (f := VarDecl.x) (lookup_mem_g hg))
        cases this with
        | head => exact hpt hm
        | tail _ h => exact not_mem_of_all_not_contains hpx hm h
      rw [rn_zip_not_mem hz, Ty.ren_congr (r1 := (dom Dm).zip Ys ++ rt) (r2 := rt)
        (fun X hX => rn_zip_not_mem (fun h => hdis X h (env.gT _ (lookup_mem_g hg) X hX)))]
      exact Gamma.lookup_append_left (env.g z _ hg)
    | none =>
      rw [Gamma.lookup_append_right hg] at hlk
      have hm := lookup_mem_g hlk
      rcases mem_zip_fst hl.symm hm with ⟨y, hy⟩
      have hy2 : List.Mem (z, y) ((ps.map VarDecl.x).zip ys) := by
        rw [List.zip_map_left]
        exact List.mem_map_of_mem (f := Prod.map VarDecl.x id) hy
      rw [rn_zip_pair hnp hy2]
      have hyy : List.Mem y ys := (List.of_mem_zip hy).2
      have hn0 : Gamma.lookup gamma' y = none := Gamma.lookup_none (fun h => by
        cases env.gx' y h with
        | head => exact hyt hyy
        | tail _ h2 => exact hyx y hyy h2)
      rw [Gamma.lookup_append_right hn0]
      refine lookup_of_mem_g ?_ ?_
      . simp only [gdom]; rw [names_renParams hl]; exact hny
      . exact List.mem_map_of_mem (f := fun p => ({ T := p.1.T.ren ((dom Dm).zip Ys ++ rt), x := p.2 } : VarDecl)) hy
  gT := by
    intro y hy X hX
    exact (List.mem_append.mp hy).elim (fun hy => List.mem_append_left _ (env.gT y hy X hX)) (fun hy => hc2 y hy X hX)
  gN := nodup_params env.gN env.gx hnp hpt hpx
  gx := scope_params env.gx
  gx' := by
    have := scope_params (ps := (ps.zip ys).map fun p => ({ T := p.1.T.ren ((dom Dm).zip Ys ++ rt), x := p.2 } : VarDecl))
      env.gx'
    rwa [names_renParams hl] at this
  kv := by
    intro p hp
    simp only [listMem_iff, List.mem_append] at hp
    rcases hp with hp | hp
    . have h12 := List.of_mem_zip hp
      exact And.intro (fun e => hpt (by rw [<- e]; exact h12.1)) (fun e => hyt (by rw [<- e]; exact h12.2))
    . exact env.kv p hp

theorem REnv.inner {rv : VRen} {rt : TRen} {Delta Delta' : Bounds} {gamma gamma' : Gamma} {Xs : List TVarName}
    {xs xs' : List VarName} (env : REnv rv rt Delta Delta' gamma gamma' Xs xs xs') {Fs : List Funnel} {Ts : List Ty}
    {Dp : Bounds} {Tp : List Ty} (hp : Pairing Delta Fs Ts Dp Tp)
    (hk : forall X, List.Mem X (Ty.ftvList (abs Fs)) -> List.Mem X Xs) (C : ClassName) :
    REnv rv rt Dp (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) (innerG gamma Fs C)
      (innerG gamma' (Fs.map (Funnel.ren rt)) C) Xs (this :: xs.filter fun x => x != this)
      (this :: xs'.filter fun x => x != this) where
  bD := fun b hb => List.mem_map_of_mem (f := fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) hb
  dX := fun X hX => env.dX X (dom_sub1 hp.sub X hX)
  dT := fun b hb => env.dT b (hp.sub b hb)
  g := by
    intro z U hl
    have hnone : forall (g : Gamma) (Fs : List Funnel),
        Gamma.lookup (withoutThis (restrict g (Ty.ftvList (abs Fs)))) this = none := by
      intro g Fs
      apply Gamma.lookup_none
      intro h
      simp only [gdom, withoutThis, listMem_iff, List.mem_map, List.mem_filter] at h
      rcases h with ⟨w, hw⟩
      have := hw.1.2
      rw [hw.2] at this
      simp at this
    by_cases hz : z = this
    . subst hz
      simp only [innerG] at hl |-
      rw [Gamma.lookup_append_right (hnone _ _), Gamma.lookup_single] at hl
      cases hl
      rw [rn_this (fun p hp => (env.kv p hp).1), Gamma.lookup_append_right (hnone _ _), Gamma.lookup_single]
      simp only [Ty.ren]
      rw [abs_ren]
    . simp only [innerG] at hl |-
      cases hg : Gamma.lookup (withoutThis (restrict gamma (Ty.ftvList (abs Fs)))) z with
      | none =>
        rw [Gamma.lookup_append_right hg, Gamma.lookup_single_ne hz] at hl
        cases hl
      | some U0 =>
        rw [Gamma.lookup_append_left hg] at hl
        cases hl
        have h1 := Gamma.lookup_of_filter (gdom_filter_nodup env.gN) hg
        have h2 := Gamma.lookup_of_filter env.gN h1.1
        have hzt : Not (rn rv z = this) := rn_ne_this (fun p hp => (env.kv p hp).2) hz
        apply Gamma.lookup_append_left
        apply Gamma.lookup_filter_of
        . apply Gamma.lookup_filter_of (env.g z _ h2.1)
          have hr := h2.2
          simp only [List.all_eq_true, List.contains_iff_mem] at hr |-
          rw [Ty.ftv_ren, abs_ren, Ty.ftvList_ren]
          intro X hX
          rcases List.mem_map.mp hX with ⟨Y, hY⟩; rw [<- hY.2]; exact List.mem_map_of_mem (hr Y hY.1)
        . simpa using hzt
  gT := by
    intro y hy X hX
    simp only [innerG, withoutThis, restrict, listMem_iff, List.mem_append, List.mem_filter, List.mem_singleton] at hy
    rcases hy with hy | hy
    . exact env.gT y hy.1.1 X hX
    . rw [hy] at hX; exact hk X hX
  gN := innerG_nodup env.gN Fs C
  gx := innerG_dom env.gx Fs C
  gx' := innerG_dom env.gx' _ C
  kv := env.kv

mutual
theorem Ty.ftv_subst_sub {s : TSubst} {A : List TVarName} : forall {T : Ty},
    (forall Y, List.Mem Y T.ftv -> forall X, List.Mem X ((Ty.var Y).subst s).ftv -> List.Mem X A) ->
    forall X, List.Mem X (T.subst s).ftv -> List.Mem X A
  | .var Y, h, X, hX => h Y (List.Mem.head _) X hX
  | .cls _ _, h, X, hX => Ty.ftvList_subst_sub h X hX
theorem Ty.ftvList_subst_sub {s : TSubst} {A : List TVarName} : forall {Ts : List Ty},
    (forall Y, List.Mem Y (Ty.ftvList Ts) -> forall X, List.Mem X ((Ty.var Y).subst s).ftv -> List.Mem X A) ->
    forall X, List.Mem X (Ty.ftvList (Ty.substList s Ts)) -> List.Mem X A
  | [], _, _, h => by cases h
  | T :: Ts, h, X, hX => by
    simp only [Ty.substList, Ty.ftvList, listMem_iff, List.mem_append] at hX h
    rcases hX with hX | hX
    . exact Ty.ftv_subst_sub (fun Y hY => h Y (Or.inl hY)) X hX
    . exact Ty.ftvList_subst_sub (fun Y hY => h Y (Or.inr hY)) X hX
end

theorem ftv_var_subst {s : TSubst} {Y X : TVarName} {U : Ty} (hl : List.lookup Y s = some U)
    (hX : List.Mem X ((Ty.var Y).subst s).ftv) : List.Mem X U.ftv := by
  simp only [Ty.subst, hl, Option.getD_some] at hX
  exact hX

theorem mem_bind_snd {A : Type} {Dl : Bounds} {Us : List A} {Y : TVarName} {U : A} (h : List.Mem (Y, U) (bind Dl Us)) :
    List.Mem U Us := (List.of_mem_zip h).2

theorem mem_bindF_snd : forall {Fs : List Funnel} {Us : List Ty} {Y : TVarName} {U : Ty},
    List.Mem (Y, U) (bindF Fs Us) -> List.Mem U Us
  | [], _, _, _, h => by simp [bindF] at h
  | _ :: _, [], _, _, h => by simp [bindF] at h
  | F :: Fs, U' :: Us, Y, U, h => by
    cases F with
    | funnel X =>
      have e : bindF (.funnel X :: Fs) (U' :: Us) = (X, U') :: bindF Fs Us := by simp [bindF]
      rw [e] at h
      cases h with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail _ (mem_bindF_snd h)
    | ground G =>
      have e : bindF (.ground G :: Fs) (U' :: Us) = bindF Fs Us := by simp [bindF]
      rw [e] at h
      exact List.Mem.tail _ (mem_bindF_snd h)

theorem ftv_bind_sub {Dl : Bounds} {Us : List Ty} {L : List Ty} (hl : Us.length = Dl.length)
    (hL : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom Dl)) :
    forall X, List.Mem X (Ty.ftvList (Ty.substList (bind Dl Us) L)) -> List.Mem X (Ty.ftvList Us) := by
  refine Ty.ftvList_subst_sub (fun Y hY X hX => ?_)
  cases bind_lookup_some hl (hL Y hY) with
  | intro U hU => exact Ty.mem_ftvList.mpr (Exists.intro U (And.intro (mem_bind_snd (lookup_mem hU)) (ftv_var_subst hU hX)))

theorem ftv_bindF_sub {Fs : List Funnel} {Us : List Ty} {L : List Ty} (hl : Us.length = Fs.length)
    (hL : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (domF Fs)) :
    forall X, List.Mem X (Ty.ftvList (Ty.substList (bindF Fs Us) L)) -> List.Mem X (Ty.ftvList Us) := by
  refine Ty.ftvList_subst_sub (fun Y hY X hX => ?_)
  cases bindF_lookup_some hl (hL Y hY) with
  | intro U hU => exact Ty.mem_ftvList.mpr (Exists.intro U (And.intro (mem_bindF_snd (lookup_mem hU)) (ftv_var_subst hU hX)))

theorem Sub.inv_subst {d : Decls} (hd : DeclOk d) {Delta Delta2 : Bounds} {s : TSubst} {A : List TVarName}
    {T1 T' : Ty} (h : Sub d Delta T1 T') : forall {C : ClassName} {Ts : List Ty}, T1 = .cls C (Ty.substList s Ts) ->
    (forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X A) ->
    exists T0, T' = T0.subst s /\ Sub d Delta2 (.cls C Ts) T0 /\ forall X, List.Mem X T0.ftv -> List.Mem X A := by
  induction h with
  | subRefl =>
    intro C Ts he hA
    subst he
    exact Exists.intro (.cls C Ts) (And.intro (by simp only [Ty.subst]) (And.intro Sub.subRefl hA))
  | @subInherit D Ts0 T' hD hl _ ih =>
    intro C Ts he hA
    simp only [Ty.cls.injEq] at he
    have e1 := he.1
    have e2 := he.2
    subst e1 e2
    have hl' : Ts.length = D.bounds.length := by rw [<- hl, substList_length]
    have heq : (Ty.cls D.C' D.Ts).subst (bind D.bounds (Ty.substList s Ts)) =
        .cls D.C' (Ty.substList s (Ty.substList (bind D.bounds Ts) D.Ts)) := by
      simp only [Ty.subst]
      rw [substList_bind_comp hl' (hd.supD D hD)]
    cases ih heq (fun X hX => ftv_bind_sub hl' (hd.supD D hD) X hX |> fun h => Ty.mem_ftvList.mp h |> fun h => by
        cases h with | intro U hU => exact hA X (Ty.mem_ftvList.mpr (Exists.intro U hU))) with
    | intro T0 h0 =>
      refine Exists.intro T0 (And.intro h0.1 (And.intro (Sub.subInherit hD hl' ?_) h0.2.2))
      exact h0.2.1
  | @subInheritLocal C0 Fs C' Ts' es Ms Ts0 T' hD hl _ ih =>
    intro C Ts he hA
    simp only [Ty.cls.injEq] at he
    have e1 := he.1
    have e2 := he.2
    subst e1 e2
    have hl' : Ts.length = Fs.length := by rw [<- hl, substList_length]
    have hcl := hd.supL _ _ _ _ _ _ hD
    have heq : (Ty.cls C' Ts').subst (bindF Fs (Ty.substList s Ts)) =
        .cls C' (Ty.substList s (Ty.substList (bindF Fs Ts) Ts')) := by
      simp only [Ty.subst]
      rw [substList_eq_map (Us := Ts'), substList_eq_map (Us := Ty.substList (bindF Fs Ts) Ts'),
        substList_eq_map (Us := Ts'), List.map_map]
      congr 1
      apply List.map_congr_left
      intro T hT
      show _ = (T.subst (bindF Fs Ts)).subst s
      exact (subst_bindF_comp hl' (fun X hX => hcl X (Ty.mem_ftvList.mpr (Exists.intro T (And.intro hT hX))))).symm
    rcases ih heq (fun X hX => by exact hA X (ftv_bindF_sub hl' hcl X hX)) with ⟨T0, h0⟩
    refine Exists.intro T0 (And.intro h0.1 (And.intro (Sub.subInheritLocal hD hl' ?_) h0.2.2))
    exact h0.2.1
  | subVar _ _ _ =>
    simp_all

theorem map_zip_fst {A B C : Type} {f : A -> C} : forall {l : List A} {l' : List B}, l'.length = l.length ->
    (l.zip l').map (fun p => f p.1) = l.map f
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [map_zip_fst (by simpa using h)]

theorem renList_subst_gen {rt : TRen} {s : TSubst} {L : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (s.map Prod.fst)) :
    Ty.renList rt (Ty.substList s L) = Ty.substList (s.map fun p => (p.1, p.2.ren rt)) L := by
  rw [Ty.renList_subst, Ty.substList_comp (fun X hX => var_subst_comp_of_some (lookup_isSome (h X hX)))]
  simp only [Ty.ren_subst]

theorem map_rn_zip : forall {xs ys : List TVarName} {r : TRen}, xs.Nodup -> xs.length = ys.length ->
    xs.map (rn (xs.zip ys ++ r)) = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, r, hn, hl => by
    simp only [List.zip_cons_cons, List.cons_append, List.map_cons, rn_cons_eq]
    have hn' := List.nodup_cons.mp hn
    have ih := map_rn_zip (r := r) hn'.2 (by simpa using hl)
    have e : xs.map (rn ((x, y) :: (xs.zip ys ++ r))) = xs.map (rn (xs.zip ys ++ r)) := by
      apply List.map_congr_left
      intro z hz
      have hzx : Not (z = x) := fun e => hn'.1 (by rw [<- e]; exact hz)
      exact rn_cons_ne hzx
    rw [e, ih]

theorem ren_vars {xs ys : List TVarName} {r : TRen} (hn : xs.Nodup) (hl : xs.length = ys.length) :
    (vars xs).map (Ty.ren (xs.zip ys ++ r)) = vars ys := by
  have e := map_rn_zip (r := r) hn hl
  simp only [vars, List.map_map]
  conv => rhs; rw [<- e]
  rw [List.map_map]
  rfl

theorem ren_disj {Xs Ys : List TVarName} {r : TRen} {Ts : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList Ts) -> Not (List.Mem X Xs)) :
    Ts.map (Ty.ren (Xs.zip Ys ++ r)) = Ty.renList r Ts := by
  rw [Ty.renList_eq_map]
  apply List.map_congr_left
  intro T hT
  exact Ty.ren_congr (fun X hX => rn_zip_not_mem (h X (Ty.mem_ftvList.mpr (Exists.intro T (And.intro hT hX)))))

theorem declMeth_closed {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {k : K} (hk : Declared d k)
    {Dl : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl} {e : Expr} (hM : List.Mem (Method.mk Dl T0 m ps e) k.Ms) :
    (forall X, List.Mem X (Ty.ftvList (cod Dl)) -> List.Mem X (k.gvars ++ dom Dl)) /\
      (forall X, List.Mem X (Ty.ftvList (T0 :: ps.map VarDecl.T)) -> List.Mem X (k.gvars ++ dom Dl)) := by
  rcases scopeExists hwf hok hk with ⟨Dk, Tk, hs⟩
  rcases scopeFacts hwf hok hs with ⟨k', hk'⟩
  have hname : k'.name = k.name := by
    rcases hk'.2.1 with ⟨Us, hUs⟩
    rcases K.generic_name k with ⟨Vs, hVs⟩; rw [hVs] at hUs; simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
  have ek := Declared.unique hwf hk'.1 hk hname
  subst ek
  rcases hk'.2.2.meths _ hM with ⟨gamma, hmo⟩
  have hmi := methodOk_inv hmo
  rw [<- hk'.2.2.gv, <- dom_append]
  refine And.intro ?_ ?_
  . intro X hX
    rcases Ty.mem_ftvList.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.1 T hT.1) X hT.2
  . intro X hX
    rcases Ty.mem_ftvList.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.2.1 T hT.1) X hT.2

theorem OverrideOkM.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {rv : VRen} {rt : TRen} {C : ClassName}
    {Us : List Ty} {M M' : Method} (h : OverrideOkM d (.cls C Us) M) (hr : RenM rv rt M M')
    (hdis : forall X, List.Mem X (Ty.ftvList Us) -> Not (List.Mem X (dom M.bounds))) (hu : M.uniq) :
    OverrideOkM d (.cls C (Ty.renList rt Us)) M' := by
  cases hr with
  | @mk _ _ Dp T0p m psp ep ep' Xs' xs' hL hl hb =>
    simp only [Method.bounds, Method.uniq] at hdis hu
    have hcod : cod ((Dp.zip Xs').map fun p => ({ X := p.2, T := p.1.T.ren ((dom Dp).zip Xs' ++ rt) } : Bound)) =
        (cod Dp).map (Ty.ren ((dom Dp).zip Xs' ++ rt)) := by
      simp only [cod, List.map_map]; exact map_zip_fst (f := fun b => b.T.ren ((dom Dp).zip Xs' ++ rt)) hL
    have hps : ((psp.zip xs').map fun p => ({ T := p.1.T.ren ((dom Dp).zip Xs' ++ rt), x := p.2 } : VarDecl)).map
        VarDecl.T = (psp.map VarDecl.T).map (Ty.ren ((dom Dp).zip Xs' ++ rt)) := by
      simp only [List.map_map]; exact map_zip_fst (f := fun p => p.T.ren ((dom Dp).zip Xs' ++ rt)) hl
    have hlenD : ((Dp.zip Xs').map fun p => ({ X := p.2, T := p.1.T.ren ((dom Dp).zip Xs' ++ rt) } : Bound)).length =
        Dp.length := by simp [hL]
    have hvars := ren_vars (r := rt) hu.1 (by rw [hL]; simp [dom])
    have hdisj := ren_disj (Ys := Xs') (r := rt) hdis
    cases h with
    | absent h1 h2 => exact OverrideOkM.absent h1 h2
    | @dec D _ _ _ _ _ _ Do T0o pso eo h1 h2 h3 h4 h5 h6 =>
      have hcl := declMeth_closed hwf hok h1 h2
      simp only [K.gvars, <- dom_append] at hcl
      have hlen : (Us ++ vars (dom Dp)).length = (D.bounds ++ Do).length := by simp [h3, h4, vars, dom]
      have hfst := bind_fst (D := D.bounds ++ Do) hlen
      refine OverrideOkM.dec h1 h2 (by rw [renList_length, h3]) (by rw [hlenD, h4]) ?_ ?_
      . rw [dom_renBounds hL, hcod, <- h5, <- Ty.renList_eq_map, renList_subst_gen (fun X hX => hfst ▸ hcl.1 X hX),
          <- bind_map, List.map_append, hvars, hdisj]
      . have e := congrArg (Ty.renList ((dom Dp).zip Xs' ++ rt)) h6
        rw [renList_subst_gen (fun X hX => hfst ▸ hcl.2 X hX), <- bind_map, List.map_append, hvars, hdisj] at e
        rw [dom_renBounds hL, e, Ty.renList, Ty.renList_eq_map, hps]
    | @loc C Fs C0 Ts0 es Ms _ _ _ _ _ _ Do T0o pso eo h1 h2 h3 h4 h5 h6 =>
      have hcl := declMeth_closed hwf hok h1 h2
      have hfst : forall X, List.Mem X (domF Fs ++ dom Do) ->
          List.Mem X ((bindF Fs Us ++ bind Do (vars (dom Dp))).map Prod.fst) := by
        intro X hX
        simp only [listMem_iff, List.mem_append, List.map_append] at hX |-
        rcases hX with hX | hX
        . cases bindF_lookup_some h3 hX with
          | intro U hU => exact Or.inl (lookup_some_mem_dom hU)
        . exact Or.inr (by rw [bind_fst (by simp [h4, vars, dom])]; exact hX)
      refine OverrideOkM.loc h1 h2 (by rw [renList_length, h3]) (by rw [hlenD, h4]) ?_ ?_
      . rw [dom_renBounds hL, hcod, <- h5, <- Ty.renList_eq_map, renList_subst_gen (fun X hX => hfst X (hcl.1 X hX)),
          List.map_append, <- bindF_map, <- bind_map, hvars, hdisj]
      . have e := congrArg (Ty.renList ((dom Dp).zip Xs' ++ rt)) h6
        rw [renList_subst_gen (fun X hX => hfst X (hcl.2 X hX)), List.map_append, <- bindF_map, <- bind_map, hvars,
          hdisj] at e
        rw [dom_renBounds hL, e, Ty.renList, Ty.renList_eq_map, hps]

theorem Consistent.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {rv : VRen} {rt : TRen}
    {C : ClassName} {Fs : List Funnel} {C0 : ClassName} {Ts : List Ty} {es es' : List Expr} {Ms Ms' : List Method}
    (h : Consistent d (.loc C Fs C0 Ts es Ms)) (hr : RenMs rv rt Ms Ms')
    (hdis : forall M, List.Mem M Ms -> forall X, List.Mem X (Ty.ftvList (abs Fs)) -> Not (List.Mem X (dom M.bounds)))
    (hu : forall M, List.Mem M Ms -> M.uniq) :
    Consistent d (.loc C (Fs.map (Funnel.ren rt)) C0 (Ty.renList rt Ts) es' Ms') := by
  rcases consistent_unfold h with ⟨Fs', Ts', es'', Ms'', h⟩
  have hcl := hd.supL _ _ _ _ _ _ h.1
  refine Exists.intro Fs' (Exists.intro Ts' (Exists.intro es'' (Exists.intro Ms'' (And.intro h.1
    (And.intro (by simp [h.2.1]) (And.intro ?_ (And.intro ?_ ?_)))))))
  . rw [abs_ren, h.2.2.1, renList_subst_gen (fun X hX => by
      cases bindF_lookup_some (Us := abs Fs) (by rw [abs_length]; exact h.2.1) (hcl X hX) with
      | intro U hU => exact lookup_some_mem_dom hU), <- bindF_map, Ty.renList_eq_map]
  . intro m; rw [RenMs.names hr]; exact h.2.2.2.1 m
  . intro M' hM'
    rw [abs_ren]
    cases RenMs.mem_inv hr hM' with
    | intro M hM => exact OverrideOkM.ren hwf hok (h.2.2.2.2 M hM.1) hM.2 (hdis M hM.1) (hu M hM.1)

theorem OverrideOk.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {rv : VRen} {rt : TRen}
    {Delta Delta' : Bounds} {C0 : ClassName} {Ts : List Ty} {Ms Ms' : List Method}
    (h : OverrideOk d Delta (.cls C0 Ts) Ms) (hr : RenMs rv rt Ms Ms')
    (hdis : forall M, List.Mem M Ms -> forall X, List.Mem X (Ty.ftvList Ts) -> Not (List.Mem X (dom M.bounds)))
    (hu : forall M, List.Mem M Ms -> M.uniq) :
    OverrideOk d Delta' (.cls C0 (Ty.renList rt Ts)) Ms' := by
  intro M' C Ts' hM' hs
  rcases RenMs.mem_inv hr hM' with ⟨M, hM⟩
  rw [Ty.renList_subst] at hs
  rcases Sub.inv_subst hd (Delta2 := Delta) (A := Ty.ftvList Ts) hs rfl (fun _ h => h) with ⟨T0, h0⟩
  cases T0 with
  | var X =>
    have e := h0.1
    rw [lookup_tS] at e
    cases e
  | cls C1 Us =>
    have e := h0.1
    simp only [Ty.subst, Ty.cls.injEq] at e
    have e1 := e.1
    subst e1
    rw [e.2, <- Ty.renList_subst]
    exact OverrideOkM.ren hwf hok (h M C Us hM.1 h0.2.1) hM.2
      (fun X hX => hdis M hM.1 X (h0.2.2 X (by simpa [Ty.ftv] using hX))) (hu M hM.1)

mutual
theorem Typing.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma e T}, Typing d Delta gamma e T ->
    forall {rv rt e' Delta' gamma' Xs xs Xs' xs'}, RenE rv rt e e' -> REnv rv rt Delta Delta' gamma gamma' Xs xs xs' ->
    e.noShadow Xs xs = true -> e'.noShadow Xs' xs' = true -> NoThis e -> NoThis e' -> e.uniq -> e'.uniq ->
    Typing d Delta' gamma' e' (T.ren rt)
  | _, _, _, _, .subs h hk hs, _, _, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' =>
    Typing.subs (Typing.ren hwf hok hd h hr env hn hn' ht ht' hu hu') (Kind.renT hd env.bD hk) (Sub.renT hd env.bD hs)
  | _, _, _, _, .var hl, _, _, _, _, _, _, _, _, _, hr, env, _, _, _, _, _, _ => by
    cases hr
    exact Typing.var (env.g _ _ hl)
  | _, _, _, _, .newObject, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _, _, _ => by
    cases hr with
    | new hs => cases hs; exact Typing.newObject
  | _, _, _, _, .declField h1 h2 h3 h4, _, _, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | field hr1 =>
      have ih := Typing.ren hwf hok hd h1 hr1 env hn hn' ht ht' hu hu'
      rw [ren_bind h4 (field_closed hok h2 h3)]
      exact Typing.declField ih h2 h3 (by rw [renList_length, h4])
  | _, _, _, _, .call (Delta0 := Delta0) (Delta1 := Delta1) (Ts2 := Ts2) (Ts1 := Ts1) h1 h2 h3 h4 h5 h6 h7 h8 h9, _, rt, _, _, _, _, _, _, _,
      hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | call hr1 hr2 =>
      simp only [Expr.noShadow, Bool.and_eq_true] at hn hn'
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht ht'
      have hcl := methodIn_closed hwf hok h2 h3
      have ih1 := Typing.ren hwf hok hd h1 hr1 env hn.1 hn'.1 ht.1 ht'.1 hu.1 hu'.1
      have ih2 := TypingSeq.ren hwf hok hd h9 hr2 env hn.2 hn'.2 ht.2 ht'.2 hu.2 hu'.2
      have hlen : (Ts2 ++ Ts1).length = (Delta0 ++ Delta1).length := by simp [h4, h5]
      have e6 := congrArg (Ty.renList rt) h6
      rw [renList_bind hlen hcl.1, renList_append] at e6
      refine Typing.call ih1 (Scope.renT h2) h3 (by rw [renList_length, h4]) (by rw [renList_length, h5]) e6
        (KindSeq.renT hd env.bD h7) ?_ ih2
      have := SubSeq.renT hd env.bD h8
      rwa [renList_bind hlen hcl.2, renList_append] at this
  | _, _, _, _, .callLbRuntime (D0 := D0) (Ts0 := Ts0) (Delta1 := Delta1) (Ts1 := Ts1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11,
      _, rt, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | superCall hr1 hr2 =>
      have hcl := methodIn_closed hwf hok (Scope.dec (Ts := Ts0) h2) h3
      have ih := TypingSeq.ren hwf hok hd h11 (RenEs.cons hr1 hr2) env
        (by simpa [Expr.noShadowList, Expr.noShadow] using hn) (by simpa [Expr.noShadowList, Expr.noShadow] using hn')
        (by simpa [NoThis, Expr.vbindersList, Expr.vbinders] using ht)
        (by simpa [NoThis, Expr.vbindersList, Expr.vbinders] using ht')
        (by simpa [Expr.uniqList, Expr.uniq] using hu) (by simpa [Expr.uniqList, Expr.uniq] using hu')
      have hlen : (Ts0 ++ Ts1).length = (D0.bounds ++ Delta1).length := by simp [h4, h5]
      have e6 := congrArg (Ty.renList rt) h6
      rw [renList_bind hlen hcl.1, renList_append] at e6
      have hs1 := Sub.renT hd env.bD h1
      have hk8 := Kind.renT hd env.bD h8
      simp only [Ty.ren] at hs1 hk8 |-
      refine Typing.callLbRuntime hs1 h2 h3 (by rw [renList_length, h4]) (by rw [renList_length, h5]) e6 h7 hk8
        (KindSeq.renT hd env.bD h9) ?_ ih
      have := SubSeq.renT hd env.bD h10
      rwa [renList_bind hlen hcl.2, renList_append] at this
  | _, _, _, _, .newTop (D := D) h1 h2 h3 h4 h5, _, _, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | new hr1 =>
      rcases RenEs.split hr1 with ⟨a, h⟩
      rcases h with ⟨b, h⟩
      have e := h.1
      subst e
      simp only [Expr.noShadow, noShadowList_append, Bool.and_eq_true] at hn hn'
      simp only [NoThis, Expr.vbinders, vbindersList_append, listMem_iff, List.mem_append, not_or] at ht ht'
      simp only [Expr.uniq, uniqList_append] at hu hu'
      have ih1 := TypingSeq.ren hwf hok hd h4 h.2.1 env hn.1 hn'.1 ht.1 ht'.1 hu.1 hu'.1
      have ih2 := Typing.ren hwf hok hd h5 (RenE.new h.2.2) env (by simpa [Expr.noShadow] using hn.2)
        (by simpa [Expr.noShadow] using hn'.2) (by simpa [NoThis, Expr.vbinders] using ht.2)
        (by simpa [NoThis, Expr.vbinders] using ht'.2) (by simpa [Expr.uniq] using hu.2)
        (by simpa [Expr.uniq] using hu'.2)
      rw [renList_bind h3 (slots_closed hok h1)] at ih1
      rw [renList_bind h3 (hd.supD D h1)] at ih2
      have hk2 := Kind.renT hd env.bD h2
      simp only [Ty.ren] at hk2 |-
      exact Typing.newTop h1 hk2 (by rw [renList_length, h3]) ih1 ih2
  | _, _, _, _, .newLocal (C := C) (Fs := Fs) (C0 := C0) (Ts := Ts) (Ms := Ms) (Delta' := Dp) h1 h2 h3 h4 h5 h6 h7 h8,
      rv, rt, _, Delta', gamma', Xs, xs, Xs', xs', hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | newLocal hr1 hr2 =>
      simp only [Expr.noShadow, Bool.and_eq_true] at hn hn'
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht ht'
      have hbq : BRen rt Dp (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) :=
        fun b hb => List.mem_map_of_mem (f := fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) hb
      have hDX : forall X, List.Mem X (dom Dp) -> List.Mem X Xs := fun X hX => env.dX X (dom_sub1 h2.sub X hX)
      have hFs : forall X, List.Mem X (Ty.ftvList (abs Fs)) -> List.Mem X Xs := fun X hX => hDX X (Kind.ftv h4 X hX)
      have hTs : forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X Xs := fun X hX => hDX X (Kind.ftv h5 X hX)
      have hdisM : forall M, List.Mem M Ms -> forall X, List.Mem X Xs -> Not (List.Mem X (dom M.bounds)) :=
        fun M hM X hX hm => Method.noShadow_dom (Method.noShadowList_mem hM hn.2) X hm hX
      have huM : forall M, List.Mem M Ms -> M.uniq := fun M hM => Method.uniqList_mem hM hu.2
      have ih6 := Typing.ren hwf hok hd h6 (RenE.new hr1) env (by simpa [Expr.noShadow] using hn.1)
        (by simpa [Expr.noShadow] using hn'.1) (by simpa [NoThis, Expr.vbinders] using ht.1)
        (by simpa [NoThis, Expr.vbinders] using ht'.1) (by simpa [Expr.uniq] using hu.1)
        (by simpa [Expr.uniq] using hu'.1)
      have hp := Pairing.renT env.bD h2
      rw [<- abs_ren] at hp
      have hk4 := Kind.renT hd hbq h4
      have hk5 := Kind.renT hd hbq h5
      simp only [Ty.ren] at hk4 hk5 |-
      rw [<- abs_ren] at hk4 |-
      refine Typing.newLocal (Consistent.ren hwf hok hd h1 hr2 (fun M hM X hX => hdisM M hM X (hFs X hX)) huM) hp
        ?_ hk4 hk5 ih6 ?_ (OverrideOk.ren hwf hok hd h8 hr2 (fun M hM X hX => hdisM M hM X (hTs X hX)) huM)
      . intro X hX
        have ec : cod (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) = Ty.renList rt (cod Dp) := by
          simp [cod, Ty.renList_eq_map]
        have ed : dom (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) = (dom Dp).map (rn rt) := by
          simp [dom]
        rw [ec, Ty.ftvList_ren] at hX
        rw [ed]
        rcases List.mem_map.mp hX with ⟨Y, hY⟩; rw [<- hY.2]; exact List.mem_map_of_mem (h3 Y hY.1)
      . intro M' hM'
        rcases RenMs.mem_inv hr2 hM' with ⟨M, hM⟩
        exact MethodOk.ren hwf hok hd (h7 M hM.1) hM.2 (env.inner h2 hFs C) (Method.noShadowList_mem hM.1 hn.2)
          (Method.noShadowList_mem hM' hn'.2) (fun h => ht.2 (Method.mem_vbindersList hM.1 h))
          (fun h => ht'.2 (Method.mem_vbindersList hM' h)) (huM M hM.1) (Method.uniqList_mem hM' hu'.2)
  | _, _, _, _, .ifInstanceof (x := x) h0 hk hc h1 h2, _, _, _, _, _, _, xs, _, xs', hr, env, hn, hn', ht, ht', hu,
      hu' => by
    cases hr with
    | @ifInst _ _ _ _ _ _ y _ _ _ _ hr0 hr1 hr2 =>
      simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn hn'
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht ht'
      have hxs : Not (List.Mem x xs) := by have := hn.1.1.2; simp at this; exact this
      have hys : Not (List.Mem y xs') := by have := hn'.1.1.2; simp at this; exact this
      have env1 := env.ext hxs hys (fun X hX => env.dX X (Kind.ftv hk X hX)) (fun e => ht.1.1.1 e.symm)
        (fun e => ht'.1.1.1 e.symm)
      exact Typing.ifInstanceof (Typing.ren hwf hok hd h0 hr0 env hn.1.1.1 hn'.1.1.1 ht.1.1.2 ht'.1.1.2 hu.1 hu'.1)
        (Kind.renT hd env.bD hk) (Cast.renT hd env.bD hc)
        (Typing.ren hwf hok hd h1 hr1 env1 hn.1.2 hn'.1.2 ht.1.2 ht'.1.2 hu.2.1 hu'.2.1)
        (Typing.ren hwf hok hd h2 hr2 env hn.2 hn'.2 ht.2 ht'.2 hu.2.2 hu'.2.2)
theorem TypingSeq.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma es Ts}, TypingSeq d Delta gamma es Ts ->
    forall {rv rt es' Delta' gamma' Xs xs Xs' xs'}, RenEs rv rt es es' ->
    REnv rv rt Delta Delta' gamma gamma' Xs xs xs' ->
    Expr.noShadowList Xs xs es = true -> Expr.noShadowList Xs' xs' es' = true ->
    Not (List.Mem this (Expr.vbindersList es)) -> Not (List.Mem this (Expr.vbindersList es')) ->
    Expr.uniqList es -> Expr.uniqList es' -> TypingSeq d Delta' gamma' es' (Ty.renList rt Ts)
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _, _, _ => by
    cases hr; exact TypingSeq.nil
  | _, _, _, _, .cons h hs, _, _, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | cons hr1 hr2 =>
      simp only [Expr.noShadowList, Bool.and_eq_true] at hn hn'
      simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ht ht'
      exact TypingSeq.cons (Typing.ren hwf hok hd h hr1 env hn.1 hn'.1 ht.1 ht'.1 hu.1 hu'.1)
        (TypingSeq.ren hwf hok hd hs hr2 env hn.2 hn'.2 ht.2 ht'.2 hu.2 hu'.2)
theorem MethodOk.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma M}, MethodOk d Delta gamma M ->
    forall {rv rt M' Delta' gamma' Xs xs Xs' xs'}, RenM rv rt M M' ->
    REnv rv rt Delta Delta' gamma gamma' Xs (this :: xs) (this :: xs') ->
    M.noShadow Xs xs = true -> M'.noShadow Xs' xs' = true -> NoThisM M -> NoThisM M' -> M.uniq -> M'.uniq ->
    MethodOk d Delta' gamma' M'
  | Delta, _, _, .methodOk (Delta' := Dm) (T0 := T0) (ps := ps) h1 h2 h3, rv, rt, _, Delta', gamma', Xs, xs, Xs',
      xs', hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | @mk _ _ _ _ _ _ _ e2 Ys ys hL hl hb =>
      simp only [Method.noShadow, Bool.and_eq_true] at hn hn'
      simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ht ht'
      simp only [Method.uniq] at hu hu'
      rw [dom_renBounds hL, names_renParams hl] at hn' hu'
      rw [names_renParams hl] at ht'
      have hc1 : forall b, List.Mem b Dm -> forall X, List.Mem X b.T.ftv -> List.Mem X (Xs ++ dom Dm) := by
        intro b hb X hX
        have := Kind.ftv (h1 b.T (List.mem_map_of_mem (f := Bound.T) hb)) X hX
        rw [dom_append] at this
        simp only [listMem_iff, List.mem_append] at this |-
        rcases this with h | h
        . exact Or.inl (env.dX X h)
        . exact Or.inr h
      have hc2 : forall p, List.Mem p ps -> forall X, List.Mem X p.T.ftv -> List.Mem X (Xs ++ dom Dm) := by
        intro p hp X hX
        have := Kind.ftv (h2 p.T (List.Mem.tail _ (List.mem_map_of_mem (f := VarDecl.T) hp))) X hX
        rw [dom_append] at this
        simp only [listMem_iff, List.mem_append] at this |-
        rcases this with h | h
        . exact Or.inl (env.dX X h)
        . exact Or.inr h
      have env2 := env.meth hL hl (fun X hX => not_mem_of_all_not_contains hn.1.1 hX)
        hn.1.2 ht.1
        (fun x hx => not_mem_of_all_not_contains hn'.1.2 hx) ht'.1 hu.1 hu.2.1 hu'.2.1 hc1 hc2
      have ih := Typing.ren hwf hok hd h3 hb env2 hn.2 hn'.2 ht.2 ht'.2 hu.2.2 hu'.2.2
      refine MethodOk.methodOk ?_ ?_ ih
      . have := KindSeq.renT hd env2.bD h1
        rw [show cod ((Dm.zip Ys).map fun p => ({ X := p.2, T := p.1.T.ren ((dom Dm).zip Ys ++ rt) } : Bound)) =
          Ty.renList ((dom Dm).zip Ys ++ rt) (cod Dm) by
            simp only [cod, List.map_map, Ty.renList_eq_map]; exact map_zip_fst (f := fun b => b.T.ren ((dom Dm).zip Ys ++ rt)) hL]
        exact this
      . have := KindSeq.renT hd env2.bD h2
        rw [show ((ps.zip ys).map fun p => ({ T := p.1.T.ren ((dom Dm).zip Ys ++ rt), x := p.2 } : VarDecl)).map
          VarDecl.T = Ty.renList ((dom Dm).zip Ys ++ rt) (ps.map VarDecl.T) by
            simp only [List.map_map, Ty.renList_eq_map]; exact map_zip_fst (f := fun p => p.T.ren ((dom Dm).zip Ys ++ rt)) hl]
        simpa only [Ty.renList] using this
end

end Funnelling
