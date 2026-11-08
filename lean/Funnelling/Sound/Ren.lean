import Funnelling.Sound.Lookup

open Funnelling.SoundSimp

namespace Funnelling.High

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
  | x :: xs => by
    simp only [List.zip_cons_cons, List.cons_append]
    exact IdRen.cons (IdRen.zip_append h xs)

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

end Funnelling.High
