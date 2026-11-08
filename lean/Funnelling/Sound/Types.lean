import Funnelling.Sound.Decl

open Funnelling.SoundSimp

namespace Funnelling.High

structure DeclOk (d : Decls) : Prop where
  supD : forall D, Declared d (.dec D) -> forall X, List.Mem X (Ty.ftvList D.Ts) -> List.Mem X (dom D.bounds)
  supL : forall C Fs C' Ts es Ms, Declared d (.loc C Fs C' Ts es Ms) ->
    forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X (domF Fs)
  scopeB : forall T Delta0 Ts0, Scope d T Delta0 Ts0 ->
    forall X, List.Mem X (Ty.ftvList (cod Delta0)) -> List.Mem X (dom Delta0)

theorem lookup_map_snd {A B : Type} [DecidableEq A] {f : B -> B} {x : A} : forall {s : List (Prod A B)},
    List.lookup x (s.map fun p => (p.1, f p.2)) = (List.lookup x s).map f
  | [] => rfl
  | (a, b) :: s => by
    simp only [List.map_cons]
    by_cases e : x = a
    . subst e; rw [lookup_cons_eq, lookup_cons_eq]; rfl
    . rw [lookup_cons_ne e, lookup_cons_ne e]; exact lookup_map_snd

mutual
theorem Ty.subst_comp {s s' : TSubst} : forall {T : Ty},
    (forall X, List.Mem X T.ftv -> ((Ty.var X).subst s).subst s' = (Ty.var X).subst (s.map fun p => (p.1, p.2.subst s'))) ->
    (T.subst s).subst s' = T.subst (s.map fun p => (p.1, p.2.subst s'))
  | .var X, h => h X (by simp [Ty.ftv])
  | .cls C Ts, h => by
    simp only [Ty.subst]
    rw [Ty.substList_comp (fun X hX => h X (by simpa [Ty.ftv] using hX))]
theorem Ty.substList_comp {s s' : TSubst} : forall {Ts : List Ty},
    (forall X, List.Mem X (Ty.ftvList Ts) ->
      ((Ty.var X).subst s).subst s' = (Ty.var X).subst (s.map fun p => (p.1, p.2.subst s'))) ->
    Ty.substList s' (Ty.substList s Ts) = Ty.substList (s.map fun p => (p.1, p.2.subst s')) Ts
  | [], _ => rfl
  | T :: Ts, h => by
    simp only [Ty.substList]
    rw [Ty.subst_comp (fun X hX => h X (List.mem_append_left _ hX)),
      Ty.substList_comp (fun X hX => h X (List.mem_append_right _ hX))]
end

theorem var_subst_comp_of_some {s s' : TSubst} {X : TVarName} (h : exists T, List.lookup X s = some T) :
    ((Ty.var X).subst s).subst s' = (Ty.var X).subst (s.map fun p => (p.1, p.2.subst s')) := by
  rcases h with ⟨T, hT⟩; simp only [Ty.subst, lookup_map_snd, hT, Option.map_some, Option.getD_some]

theorem bind_map {A : Type} {f : A -> A} {Delta : Bounds} {Us : List A} :
    bind Delta (Us.map f) = (bind Delta Us).map fun p => (p.1, f p.2) := by
  simp only [bind]
  rw [List.zip_map_right]
  rfl

theorem bindF_map {f : Ty -> Ty} : forall {Fs : List Funnel} {Us : List Ty},
    bindF Fs (Us.map f) = (bindF Fs Us).map fun p => (p.1, f p.2)
  | [], _ => by simp [bindF]
  | _ :: _, [] => by simp [bindF]
  | F :: Fs, U :: Us => by
    cases F with
    | ground G =>
      simp only [bindF, List.map_cons, List.zip_cons_cons, List.filterMap_cons] at |-
      exact bindF_map (Fs := Fs) (Us := Us)
    | funnel X =>
      simp only [bindF, List.map_cons, List.zip_cons_cons, List.filterMap_cons, List.cons.injEq, true_and] at |-
      exact bindF_map (Fs := Fs) (Us := Us)

theorem bind_lookup_some {A : Type} {Delta : Bounds} {Us : List A} {X : TVarName} (hl : Us.length = Delta.length)
    (hX : List.Mem X (dom Delta)) : exists U, List.lookup X (bind Delta Us) = some U := by
  apply lookup_isSome
  simp only [bind]
  rw [zip_map_fst (by simp [dom, hl])]
  exact hX

theorem bindF_lookup_some : forall {Fs : List Funnel} {Us : List Ty} {X : TVarName}, Us.length = Fs.length ->
    List.Mem X (domF Fs) -> exists U, List.lookup X (bindF Fs Us) = some U
  | [], _, _, _, h => by simp [domF] at h
  | _ :: _, [], _, hl, _ => by simp at hl
  | F :: Fs, U :: Us, X, hl, hX => by
    rw [domF_cons] at hX
    cases F with
    | ground G =>
      simp only [bindF, List.zip_cons_cons, List.filterMap_cons]
      rw [show domF [Funnel.ground G] = [] from rfl, List.nil_append] at hX
      exact bindF_lookup_some (by simpa using hl) hX
    | funnel Y =>
      simp only [bindF, List.zip_cons_cons, List.filterMap_cons]
      by_cases e : X = Y
      . subst e; exact Exists.intro U lookup_cons_eq
      . rw [lookup_cons_ne e]
        simp only [domF, List.filterMap_cons, List.filterMap_nil, listMem_iff, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hX
        rcases hX with h | h
        . exact absurd h e
        . exact bindF_lookup_some (by simpa using hl) h

theorem subst_bind_comp {s' : TSubst} {Delta : Bounds} {Us : List Ty} {T : Ty} (hl : Us.length = Delta.length)
    (hT : forall X, List.Mem X T.ftv -> List.Mem X (dom Delta)) :
    (T.subst (bind Delta Us)).subst s' = T.subst (bind Delta (Ty.substList s' Us)) := by
  rw [substList_eq_map, bind_map]
  exact Ty.subst_comp (fun X hX => var_subst_comp_of_some (bind_lookup_some hl (hT X hX)))

theorem substList_bind_comp {s' : TSubst} {Delta : Bounds} {Us Ts : List Ty} (hl : Us.length = Delta.length)
    (hT : forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X (dom Delta)) :
    Ty.substList s' (Ty.substList (bind Delta Us) Ts) = Ty.substList (bind Delta (Ty.substList s' Us)) Ts := by
  rw [substList_eq_map (Us := Us), bind_map]
  exact Ty.substList_comp (fun X hX => var_subst_comp_of_some (bind_lookup_some hl (hT X hX)))

theorem subst_bindF_comp {s' : TSubst} {Fs : List Funnel} {Us : List Ty} {T : Ty} (hl : Us.length = Fs.length)
    (hT : forall X, List.Mem X T.ftv -> List.Mem X (domF Fs)) :
    (T.subst (bindF Fs Us)).subst s' = T.subst (bindF Fs (Ty.substList s' Us)) := by
  rw [substList_eq_map, bindF_map]
  exact Ty.subst_comp (fun X hX => var_subst_comp_of_some (bindF_lookup_some hl (hT X hX)))

theorem substList_length {s : TSubst} {Ts : List Ty} : (Ty.substList s Ts).length = Ts.length := by
  rw [substList_eq_map]; simp

theorem Sub.subst {d : Decls} (hd : DeclOk d) {Delta Delta' : Bounds} {s : TSubst}
    (hb : forall b, List.Mem b Delta -> Sub d Delta' ((Ty.var b.X).subst s) (b.T.subst s)) {T1 T2 : Ty}
    (h : Sub d Delta T1 T2) : Sub d Delta' (T1.subst s) (T2.subst s) := by
  induction h with
  | subRefl => exact Sub.subRefl
  | @subInherit D Ts0 T' hD hl _ ih =>
    rw [subst_bind_comp hl (fun X hX => hd.supD D hD X (by simpa [Ty.ftv] using hX))] at ih
    simp only [Ty.subst]
    exact Sub.subInherit hD (by rw [substList_length, hl]) ih
  | @subInheritLocal C Fs C' Ts' es Ms Ts T' hD hl _ ih =>
    rw [subst_bindF_comp hl (fun X hX => hd.supL C Fs C' Ts' es Ms hD X (by simpa [Ty.ftv] using hX))] at ih
    simp only [Ty.subst]
    exact Sub.subInheritLocal hD (by rw [substList_length, hl]) ih
  | @subVar X T T' hm _ ih => exact (hb { X := X, T := T } hm).trans ih

theorem Sub.mono {d : Decls} {Delta Delta' : Bounds} (hs : Sub1 Delta Delta') {T1 T2 : Ty}
    (h : Sub d Delta T1 T2) : Sub d Delta' T1 T2 := by
  induction h with
  | subRefl => exact Sub.subRefl
  | subInherit hD hl _ ih => exact Sub.subInherit hD hl ih
  | subInheritLocal hD hl _ ih => exact Sub.subInheritLocal hD hl ih
  | subVar hm _ ih => exact Sub.subVar (hs _ hm) ih

theorem Sub.cls_indep {d : Decls} {Delta Delta' : Bounds} {C : ClassName} {Ts : List Ty} {T : Ty}
    (h : Sub d Delta (.cls C Ts) T) : Sub d Delta' (.cls C Ts) T := by
  generalize he : Ty.cls C Ts = T0 at h
  induction h generalizing C Ts with
  | subRefl => exact Sub.subRefl
  | subInherit hD hl _ ih => cases he; exact Sub.subInherit hD hl (ih rfl)
  | subInheritLocal hD hl _ ih => cases he; exact Sub.subInheritLocal hD hl (ih rfl)
  | subVar => cases he

mutual
theorem Ty.subst_id {s : TSubst} : forall {T : Ty}, (forall X, List.Mem X T.ftv -> (Ty.var X).subst s = Ty.var X) ->
    T.subst s = T
  | .var X, h => h X (by simp [Ty.ftv])
  | .cls C Ts, h => by
    simp only [Ty.subst]
    rw [Ty.substList_id (fun X hX => h X (by simpa [Ty.ftv] using hX))]
theorem Ty.substList_id {s : TSubst} : forall {Ts : List Ty},
    (forall X, List.Mem X (Ty.ftvList Ts) -> (Ty.var X).subst s = Ty.var X) -> Ty.substList s Ts = Ts
  | [], _ => rfl
  | T :: Ts, h => by
    simp only [Ty.substList]
    rw [Ty.subst_id (fun X hX => h X (List.mem_append_left _ hX)),
      Ty.substList_id (fun X hX => h X (List.mem_append_right _ hX))]
end

theorem GTy.subst_ty {s : TSubst} (G : GTy) : G.ty.subst s = G.ty :=
  Ty.subst_id (fun X hX => by rw [GTy.ftv_ty] at hX; cases hX)

theorem Pairing.subst {s : TSubst} {Delta : Bounds} {Fs : List Funnel} {Ts : List Ty} {Delta0 : Bounds}
    {Ts0 : List Ty} (h : Pairing Delta Fs Ts Delta0 Ts0) :
    Pairing Delta Fs (Ty.substList s Ts) Delta0 (Ty.substList s Ts0) := by
  induction h with
  | nil => exact Pairing.nil
  | funnel hm _ ih => exact Pairing.funnel hm ih
  | @ground G Fs Ts Delta' Ts' _ ih =>
    simp only [Ty.substList]
    rw [GTy.subst_ty]
    exact Pairing.ground ih

theorem Scope.subst {d : Decls} {s : TSubst} {T : Ty} {Delta0 : Bounds} {Ts0 : List Ty}
    (h : Scope d T Delta0 Ts0) : Scope d (T.subst s) Delta0 (Ty.substList s Ts0) := by
  cases h with
  | dec hD => simp only [Ty.subst]; exact Scope.dec hD
  | loc h1 h2 h3 h4 h5 => simp only [Ty.subst]; exact Scope.loc h1 h2 h3 h4 h5.subst

theorem Kind.ftv {d : Decls} {Delta : Bounds} {T : Ty} (h : Kind d Delta T) :
    forall X, List.Mem X T.ftv -> List.Mem X (dom Delta) := by
  induction h with
  | @wfVar X T hm =>
    intro Y hY
    have e : Y = X := by simpa [Ty.ftv] using hY
    subst e
    exact List.mem_map_of_mem (f := Bound.X) hm
  | @wfClass C Ts Delta0 Ts0 _ _ _ _ ih =>
    intro Y hY
    simp only [Ty.ftv] at hY
    rcases (ftvList_mem.mp hY) with ⟨T, hT⟩; exact ih T hT.1 Y hT.2

theorem Kind.mono {d : Decls} {Delta Delta' : Bounds} (hs : Sub1 Delta Delta') {T : Ty}
    (h : Kind d Delta T) : Kind d Delta' T := by
  induction h with
  | wfVar hm => exact Kind.wfVar (hs _ hm)
  | wfClass h1 _ h3 h4 ih => exact Kind.wfClass h1 ih h3 (seq2_mono h4)
where
  seq2_mono {Ts Us : List Ty} (h : SubSeq d Delta Ts Us) : SubSeq d Delta' Ts Us := by
    induction h with
    | nil => exact Seq2.nil
    | cons h1 _ ih => exact Seq2.cons (h1.mono hs) ih

theorem SubSeq.subst {d : Decls} (hd : DeclOk d) {Delta Delta' : Bounds} {s : TSubst}
    (hb : forall b, List.Mem b Delta -> Sub d Delta' ((Ty.var b.X).subst s) (b.T.subst s)) {Ts Us : List Ty}
    (h : SubSeq d Delta Ts Us) : SubSeq d Delta' (Ty.substList s Ts) (Ty.substList s Us) := by
  induction h with
  | nil => exact Seq2.nil
  | cons h1 _ ih => exact Seq2.cons (Sub.subst hd hb h1) ih

theorem Kind.subst {d : Decls} (hd : DeclOk d) {Delta Delta' : Bounds} {s : TSubst}
    (hb : forall b, List.Mem b Delta -> Sub d Delta' ((Ty.var b.X).subst s) (b.T.subst s))
    (hk : forall b, List.Mem b Delta -> Kind d Delta' ((Ty.var b.X).subst s)) {T : Ty}
    (h : Kind d Delta T) : Kind d Delta' (T.subst s) := by
  induction h with
  | @wfVar X T hm => exact hk { X := X, T := T } hm
  | @wfClass C Ts Delta0 Ts0 h1 _ h3 h4 ih =>
    have hsc := h1.subst (s := s)
    simp only [Ty.subst] at hsc |-
    refine Kind.wfClass hsc ?_ (by rw [substList_length, h3]) ?_
    . intro T hT
      rw [substList_eq_map] at hT
      rcases List.mem_map.mp hT with ⟨U, hU⟩; rw [<- hU.2]; exact ih U hU.1
    . have := SubSeq.subst hd hb h4
      rwa [substList_bind_comp h3 (hd.scopeB _ _ _ h1)] at this

end Funnelling.High