import Funnelling.Sound.Declared

open Funnelling.SoundSimp

namespace Funnelling

structure DeclOk (d : Decls) : Prop where
  supD : forall D, Declared d (.dec D) -> forall X, List.Mem X (Ty.ftvList D.Ts) -> List.Mem X (dom D.Delta)
  supL : forall C Fs C' Ts es Ms, Declared d (.newLocal C Fs C' Ts es Ms) ->
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
    exact Sub.subInherit hD (by rw [substList_length, hl]) ih
  | @subInheritLocal C Fs C' Ts' es Ms Ts T' hD hl _ ih =>
    rw [subst_bindF_comp hl (fun X hX => hd.supL C Fs C' Ts' es Ms hD X (by simpa [Ty.ftv] using hX))] at ih
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
  | newLocal h1 h2 h3 h4 h5 => simp only [Ty.subst]; exact Scope.newLocal h1 h2 h3 h4 h5.subst

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
    rcases (Ty.mem_ftvList.mp hY) with ⟨T, hT⟩; exact ih T hT.1 Y hT.2

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

abbrev RenCtx (Delta Delta' : Bounds) (s : TSubst) : Prop :=
  forall b, List.Mem b Delta -> exists X', (Ty.var b.X).subst s = Ty.var X' /\ List.Mem { X := X', T := b.T.subst s } Delta'

theorem RenCtx.sub {d : Decls} {Delta Delta' : Bounds} {s : TSubst} (h : RenCtx Delta Delta' s) :
    forall b, List.Mem b Delta -> Sub d Delta' ((Ty.var b.X).subst s) (b.T.subst s) := by
  intro b hb
  rcases h b hb with ⟨X', hX⟩; rw [hX.1]; exact Sub.subVar hX.2 Sub.subRefl

theorem RenCtx.kind {d : Decls} {Delta Delta' : Bounds} {s : TSubst} (h : RenCtx Delta Delta' s) :
    forall b, List.Mem b Delta -> Kind d Delta' ((Ty.var b.X).subst s) := by
  intro b hb
  rcases h b hb with ⟨X', hX⟩; rw [hX.1]; exact Kind.wfVar hX.2

theorem Cast.ren {d : Decls} (hd : DeclOk d) {Delta Delta' : Bounds} {s : TSubst} (hr : RenCtx Delta Delta' s)
    {T0 T : Ty} (h : Cast d Delta T0 T) : Cast d Delta' (T0.subst s) (T.subst s) := by
  induction h with
  | castUp h1 => exact Cast.castUp (Sub.subst hd hr.sub h1)
  | @castVar X T T' hm _ ih =>
    rcases hr { X := X, T := T } hm with ⟨X', hX⟩
    rw [hX.1]
    exact Cast.castVar hX.2 ih
  | castDown h1 h2 h3 h4 =>
    have := Sub.subst hd hr.sub h1
    simp only [Ty.subst] at this |-
    exact Cast.castDown this h2 h3 h4

abbrev SubstCtx (d : Decls) (Delta Delta' : Bounds) (s : TSubst) : Prop :=
  forall b, List.Mem b Delta ->
    (exists X', (Ty.var b.X).subst s = Ty.var X' /\ List.Mem { X := X', T := b.T.subst s } Delta') \/
    (Sub d Delta' ((Ty.var b.X).subst s) (b.T.subst s) /\ Kind d Delta' ((Ty.var b.X).subst s) /\
      Kind d Delta' (b.T.subst s))

theorem SubstCtx.sub {d : Decls} {Delta Delta' : Bounds} {s : TSubst} (h : SubstCtx d Delta Delta' s) :
    forall b, List.Mem b Delta -> Sub d Delta' ((Ty.var b.X).subst s) (b.T.subst s) := by
  intro b hb
  rcases h b hb with h' | h'
  . cases h' with
    | intro X' hX => rw [hX.1]; exact Sub.subVar hX.2 Sub.subRefl
  . exact h'.1

theorem SubstCtx.kind {d : Decls} {Delta Delta' : Bounds} {s : TSubst} (h : SubstCtx d Delta Delta' s) :
    forall b, List.Mem b Delta -> Kind d Delta' ((Ty.var b.X).subst s) := by
  intro b hb
  rcases h b hb with h' | h'
  . cases h' with
    | intro X' hX => rw [hX.1]; exact Kind.wfVar hX.2
  . exact h'.2.1

theorem Cast.gsub {d : Decls} (hd : DeclOk d) {Delta Delta' : Bounds} {s : TSubst} (hc : SubstCtx d Delta Delta' s)
    {T0 T : Ty} (h : Cast d Delta T0 T) : exists T1, Sub d Delta' (T0.subst s) T1 /\ Cast d Delta' T1 (T.subst s) /\
      (T1 = T0.subst s \/ Kind d Delta' T1) := by
  induction h with
  | castUp h1 =>
    exact Exists.intro _ (And.intro Sub.subRefl (And.intro (Cast.castUp (Sub.subst hd hc.sub h1)) (Or.inl rfl)))
  | @castVar X T T' hm _ ih =>
    rcases ih with ⟨T1, hT1⟩
    rcases hc { X := X, T := T } hm with h' | h'
    . rcases h' with ⟨X', hX⟩
      rcases hT1.2.2 with e | hk
      . rw [hX.1]
        refine Exists.intro (Ty.var X') (And.intro Sub.subRefl (And.intro ?_ (Or.inl rfl)))
        rw [e] at hT1
        exact Cast.castVar hX.2 hT1.2.1
      . refine Exists.intro T1 (And.intro ?_ (And.intro hT1.2.1 (Or.inr hk)))
        rw [hX.1]
        exact Sub.subVar hX.2 hT1.1
    . refine Exists.intro T1 (And.intro (h'.1.trans hT1.1) (And.intro hT1.2.1 ?_))
      rcases hT1.2.2 with e | hk
      . rw [e]; exact Or.inr h'.2.2
      . exact Or.inr hk
  | castDown h1 h2 h3 h4 =>
    have := Sub.subst hd hc.sub h1
    simp only [Ty.subst] at this |-
    exact Exists.intro _ (And.intro Sub.subRefl (And.intro (Cast.castDown this h2 h3 h4) (Or.inl rfl)))

def ClassDecl.gvars : ClassDecl -> List TVarName
  | .dec D => dom D.Delta
  | .newLocal _ Fs _ _ _ _ => domF Fs

structure SF (d : Decls) (K : ClassDecl) (Delta0 : Bounds) : Prop where
  closedB : forall X, List.Mem X (Ty.ftvList (cod Delta0)) -> List.Mem X (dom Delta0)
  ndom : (dom Delta0).Nodup
  gv : dom Delta0 = K.gvars
  meths : forall M, List.Mem M K.Ms -> exists Gamma, MethodOk d Delta0 Gamma M
  ns : forall M, List.Mem M K.Ms -> exists Xs xs, Sub1 (dom Delta0) Xs /\ Method.noShadow Xs xs M = true
  sup : forall C Fs C' Ts es Ms, K = .newLocal C Fs C' Ts es Ms -> forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X (domF Fs)
  supK : forall C Fs C' Ts es Ms, K = .newLocal C Fs C' Ts es Ms -> Kind d Delta0 (.cls C' Ts)

theorem methodOk_inv {d : Decls} {Delta : Bounds} {Gamma : TypeEnv} {Delta' : Bounds} {T0 : Ty} {m : MethName}
    {ps : List VarDecl} {e : Expr} (h : MethodOk d Delta Gamma (.mk Delta' T0 m ps e)) :
    KindSeq d (Delta ++ Delta') (cod Delta') /\ KindSeq d (Delta ++ Delta') (T0 :: ps.map VarDecl.T) /\
      Typing d (Delta ++ Delta') (Gamma ++ ps) e T0 := by
  cases h with
  | methodOk h1 h2 h3 => exact And.intro h1 (And.intro h2 h3)

theorem sf_dec {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {D : Dec} (hD : Declared d (.dec D)) :
    SF d (.dec D) D.Delta := by
  have hc := hok D hD.dec_mem
  refine { closedB := ?_, ndom := ?_, gv := rfl, meths := ?_, ns := ?_, sup := ?_, supK := ?_ }
  . intro X hX
    rcases Ty.mem_ftvList.mp hX with ⟨T, hT⟩; exact Kind.ftv (hc.1 T hT.1) X hT.2
  . exact hwf.2.2.2.2.1 D.Delta (by
      simp only [listMem_iff, List.mem_append, List.mem_map]
      exact Or.inl (Exists.intro D (And.intro hD.dec_mem rfl)))
  . intro M hM; exact Exists.intro _ (hc.2.2.1 M hM)
  . intro M hM
    exact Exists.intro (dom D.Delta) (Exists.intro [] (And.intro (fun _ h => h)
      (Method.noShadowList_mem hM (hwf.2.2.2.2.2.2.1 D hD.dec_mem))))
  . intro _ _ _ _ _ _ e; cases e
  . intro _ _ _ _ _ _ e; cases e

theorem methods_mem {d : Decls} {K : ClassDecl} (hk : Declared d K) {M : Method} (hM : List.Mem M K.Ms) :
    List.Mem M d.methods := by
  simp only [Decls.methods, listMem_iff, List.mem_flatMap]
  exact Exists.intro K (And.intro hk.mem hM)

theorem scopeFacts {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {T : Ty} {Delta0 : Bounds} {Ts0 : List Ty}
    (h : Scope d T Delta0 Ts0) : exists K, Declared d K /\ (exists Us, T = .cls K.name Us) /\ SF d K Delta0 := by
  induction h with
  | @dec D Ts hD => exact Exists.intro (.dec D) (And.intro hD (And.intro (Exists.intro Ts rfl) (sf_dec hwf hok hD)))
  | @newLocal C Delta' T0 m ps e C0 Fs C' Ts' es Ms T Delta Ts'' Ts Delta0 Ts0 h1 h2 h3 h4 h5 ih =>
    rcases ih with ⟨K', hk'⟩
    rcases h1 with ⟨K'', hk''⟩
    have hgen : K'.name = C := by
      rcases hk'.2.1 with ⟨Us, hUs⟩
      cases h3 with
      | dec hD => simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
      | newLocal hD => simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
    have ek := Declared.unique hwf hk''.1 hk'.1 (by rw [hk''.2.1, hgen])
    subst ek
    have sf := hk'.2.2
    have hM := hk''.2.2
    rcases sf.meths _ hM with ⟨Gamma, hmo⟩
    have hmi := methodOk_inv hmo
    rcases h2 with ⟨E, hE⟩
    rw [hE] at hmi
    rcases occ_typing E hmi.2.2 with ⟨Gamma', hg⟩
    rcases hg with ⟨Ta, hTa⟩
    rcases inv_local hTa rfl with ⟨w, hw⟩
    have hdecl : Declared d (.newLocal C0 Fs C' Ts' es Ms) :=
      Declared.newLocal hk''.1 hM (Exists.intro E hE)
    rcases sf.ns _ hM with ⟨Xs, hXs⟩
    rcases hXs with ⟨xs, hxs⟩
    have hns := hxs.2
    simp only [Method.noShadow, Bool.and_eq_true] at hns
    have hnd : (dom (Delta ++ Delta')).Nodup := by
      rw [dom_append]
      apply List.nodup_append.mpr
      refine And.intro sf.ndom (And.intro ?_ ?_)
      . exact hwf.2.2.2.2.1 Delta' (by
          simp only [listMem_iff, List.mem_append, List.mem_map]
          exact Or.inr (Exists.intro _ (And.intro (methods_mem hk''.1 hM) rfl)))
      . intro X hX Y hY e
        subst e
        exact not_mem_of_all_not_contains hns.1.1 hY (hxs.1 X hX)
    have eD := Pairing.unique hnd h5 hw.pair
    subst eD
    refine Exists.intro (.newLocal C0 Fs C' Ts' es Ms) (And.intro hdecl (And.intro (Exists.intro Ts rfl) ?_))
    refine { closedB := hw.closedB, ndom := ?_, gv := h5.dom_eq, meths := ?_, ns := ?_, sup := ?_, supK := ?_ }
    . rw [h5.dom_eq]; exact hwf.2.2.2.2.2.1 _ hdecl.mem
    . intro M' hM'; exact Exists.intro _ (hw.meths M' hM')
    . intro M' hM'
      have hn2 := hns.2
      rw [hE] at hn2
      rcases occ_noShadow E hn2 with ⟨xs', hxs'⟩
      refine Exists.intro (Xs ++ dom Delta') (Exists.intro xs' (And.intro ?_ (Method.noShadowList_mem hM' hxs')))
      intro X hX
      have hX2 : List.Mem X (dom (Delta ++ Delta')) := by
        have := h5.sub
        simp only [dom] at hX |-
        rcases List.mem_map.mp hX with ⟨b, hb⟩; rw [<- hb.2]; exact List.mem_map_of_mem (this b hb.1)
      rw [dom_append] at hX2
      simp only [listMem_iff, List.mem_append] at hX2 |-
      rcases hX2 with h | h
      . exact Or.inl (hxs.1 X h)
      . exact Or.inr h
    . intro C1 Fs1 C1' Ts1 es1 Ms1 e X hX
      cases e
      have := Kind.ftv hw.kindS X (by simpa [Ty.ftv] using hX)
      rwa [h5.dom_eq] at this
    . intro C1 Fs1 C1' Ts1 es1 Ms1 e
      cases e
      exact hw.kindS

def ClassDecl.generic : ClassDecl -> Ty
  | .dec D => .cls D.C (vars (dom D.Delta))
  | .newLocal C Fs _ _ _ _ => .cls C (vars (domF Fs))

theorem ClassDecl.generic_name (K : ClassDecl) : exists Us, K.generic = .cls K.name Us := by cases K <;> exact Exists.intro _ rfl

theorem Declared.generic {d : Decls} {K : ClassDecl} (hk : Declared d K) : Generic d K.name K.generic := by
  cases K with
  | dec D => exact Generic.dec hk
  | newLocal C Fs C' Ts es Ms => exact Generic.newLocal hk

theorem scopeExists {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {K : ClassDecl} (hk : Declared d K) :
    exists Delta0 Ts0, Scope d K.generic Delta0 Ts0 := by
  induction hk with
  | @dec D hD => exact Exists.intro _ (Exists.intro _ (Scope.dec (Declared.dec hD)))
  | @newLocal K Delta T0 m ps e C0 Fs C' Ts es Ms hk hM hO ih =>
    rcases ih with ⟨Dk, h⟩
    rcases h with ⟨Tk, hs⟩
    rcases scopeFacts hwf hok hs with ⟨K', hk'⟩
    have hname : K'.name = K.name := by
      rcases hk'.2.1 with ⟨Us, hUs⟩
      rcases ClassDecl.generic_name K with ⟨Vs, hVs⟩; rw [hVs] at hUs; simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
    have ek := Declared.unique hwf hk'.1 hk hname
    subst ek
    rcases hk'.2.2.meths _ hM with ⟨Gamma, hmo⟩
    have hmi := methodOk_inv hmo
    rcases hO with ⟨E, hE⟩
    rw [hE] at hmi
    rcases occ_typing E hmi.2.2 with ⟨Gamma', hg⟩
    rcases hg with ⟨Ta, hTa⟩
    rcases inv_local hTa rfl with ⟨w, hw⟩
    have hdecl : Declared d (.newLocal C0 Fs C' Ts es Ms) := Declared.newLocal hk hM (Exists.intro E hE)
    have hab := abs_funnels (Fs := Fs) (fun F hF => hwf.2.2.2.2.2.2.2.2.2.2 _ hdecl.mem F hF)
    have hp := hw.pair
    rw [hab] at hp
    exact Exists.intro _ (Exists.intro _ (Scope.newLocal (Exists.intro K' (And.intro hk (And.intro rfl hM)))
      (Exists.intro E hE) hk.generic hs hp))

theorem declOk {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) : DeclOk d where
  supD := by
    intro D hD X hX
    exact Kind.ftv ((hok D hD.dec_mem).2.1 _ (List.Mem.head _)) X (by simpa [Ty.ftv] using hX)
  supL := by
    intro C Fs C' Ts es Ms hD X hX
    rcases scopeExists hwf hok hD with ⟨Dk, h⟩
    rcases h with ⟨Tk, hs⟩
    rcases scopeFacts hwf hok hs with ⟨K', hk'⟩
    have hname : K'.name = C := by
      rcases hk'.2.1 with ⟨Us, hUs⟩; simp only [ClassDecl.generic, Ty.cls.injEq] at hUs; exact hUs.1.symm
    have ek := Declared.unique hwf hk'.1 hD hname
    exact hk'.2.2.sup C Fs C' Ts es Ms ek X hX
  scopeB := by
    intro T Delta0 Ts0 hs
    rcases scopeFacts hwf hok hs with ⟨K', hk'⟩; exact hk'.2.2.closedB

end Funnelling
