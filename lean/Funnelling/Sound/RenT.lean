import Funnelling.Sound.VSubT

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
  rcases ftvList_mem.mp hX with ⟨T, hT⟩; exact Kind.ftv ((hok D hD.dec_mem).2.1 T (List.Mem.tail _ hT.1)) X hT.2

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
    rcases ftvList_mem.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.2.1 T hT.1) X hT.2
  . intro X hX
    rcases ftvList_mem.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.1 T hT.1) X hT.2

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

end Funnelling
