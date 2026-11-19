import Funnelling.Sound.CheckedCast

open Funnelling.SoundSimp

namespace Funnelling

theorem lookup_zip_vars {X : TVarName} : forall {Xs : List TVarName}, List.Mem X Xs ->
    List.lookup X (Xs.zip (vars Xs)) = some (Ty.var X)
  | [], h => by cases h
  | Y :: Xs, h => by
    simp only [vars, List.map_cons, List.zip_cons_cons]
    by_cases e : X = Y
    . subst e; exact lookup_cons_eq
    . rw [lookup_cons_ne e]
      cases h with
      | head => exact absurd rfl e
      | tail _ h => exact lookup_zip_vars h

theorem substList_bind_vars_id {Dl : Bounds} {L : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom Dl)) :
    Ty.substList (bind Dl (vars (dom Dl))) L = L := by
  apply Ty.substList_id
  intro X hX
  simp only [Ty.subst, bind, lookup_zip_vars (h X hX), Option.getD_some]

theorem vars_append {Xs Ys : List TVarName} : vars (Xs ++ Ys) = vars Xs ++ vars Ys := by simp [vars]

theorem ftv_vars {X : TVarName} {Xs : List TVarName} (h : List.Mem X (Ty.ftvList (vars Xs))) : List.Mem X Xs := by
  rcases Ty.mem_ftvList.mp h with ⟨T, hT⟩
  simp only [vars, listMem_iff, List.mem_map] at hT
  rcases hT.1 with ⟨Y, hY⟩; rw [<- hY.2] at hT; have := hT.2; simp [Ty.ftv] at this; rw [this]; exact hY.1

theorem dec_override {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {D : Dec}
    (hD : Declared d (.dec D)) {M : Method} (hM : List.Mem M D.Ms) {D0 : Dec} (hD0 : Declared d (.dec D0))
    {Gs Ts0 : List Ty} (hl : Gs.length = D.Delta.length) (hs : Sub d [] (.cls D.C Gs) (.cls D0.C Ts0)) :
    exists Us, Ts0 = Ty.substList (bind D.Delta Gs) Us /\ OverrideOkM d (.cls D0.C Us) M /\
      forall X, List.Mem X (Ty.ftvList Us) -> List.Mem X (dom D.Delta) := by
  have hn := (sf_dec hwf hok hD).ndom
  have e : Gs = Ty.substList (bind D.Delta Gs) (vars (dom D.Delta)) :=
    (vars_subst hn (by rw [hl]; simp [dom])).symm
  rw [e] at hs
  rcases Sub.inv_subst hd (Delta2 := D.Delta) (A := dom D.Delta) hs rfl (fun X hX => ftv_vars hX) with ⟨T0, h0⟩
  rcases Sub.cls_target h0.2.1 rfl with ⟨C1, U0, e0⟩
  subst e0
  have e1 := h0.1
  simp only [Ty.subst, Ty.cls.injEq] at e1
  have e2 := e1.1
  subst e2
  refine Exists.intro U0 (And.intro e1.2 (And.intro ?_ h0.2.2))
  rcases Sub.dec_step hwf hD h0.2.1 with e3 | e3
  . simp only [Ty.cls.injEq] at e3
    have eD := Declared.unique hwf hD hD0 e3.1.symm
    cases eD
    rw [e3.2]
    cases M with
    | mk Dm T0m m ps e =>
      have hcl := methodIn_closed hwf hok (Scope.dec hD) ⟨.dec D, hD, rfl, hM⟩
      have hv : vars (dom D.Delta) ++ vars (dom Dm) = vars (dom (D.Delta ++ Dm)) := by rw [dom_append, vars_append]
      refine OverrideOkM.found ⟨.dec D, hD, rfl, hM⟩ (Scope.dec hD) (by simp [vars, dom]) rfl ?_ ?_
      . rw [hv, substList_bind_vars_id hcl.2]
      . rw [hv, substList_bind_vars_id hcl.1]
  . have hsup : (Ty.cls D.C' D.Ts).subst (bind D.Delta (vars (dom D.Delta))) = Ty.cls D.C' D.Ts := by
      simp only [Ty.subst]
      rw [substList_bind_vars_id (hd.supD D hD)]
    rw [hsup] at e3
    exact (hok D hD.dec_mem).2.2.2 M D0.C U0 hM e3.2

theorem found_sig {d : Decls} (hwf : WFDecls d) {C0 : ClassName} {Ts0 : List Ty} {Delta0 : Bounds}
    {Delta1 : Bounds} {T0c : Ty} {m : MethName} {psc : List VarDecl} {body : Expr} {Dp : Bounds} {T0 : Ty}
    {ps : List VarDecl} {e : Expr} (hs : Scope d C0 Delta0)
    (hm : MethodIn d (.mk Delta1 T0c m psc body) C0)
    (hO : OverrideOkM d (.cls C0 Ts0) (.mk Dp T0 m ps e)) :
    Dp.length = Delta1.length /\
      Ty.substList (bind (Delta0 ++ Delta1) (Ts0 ++ vars (dom Dp))) (cod Delta1) = cod Dp /\
      Ty.substList (bind (Delta0 ++ Delta1) (Ts0 ++ vars (dom Dp))) (T0c :: psc.map VarDecl.T) =
        T0 :: ps.map VarDecl.T := by
  rcases hm with ⟨K, hk, hkn, hkM⟩
  generalize hTT : Ty.cls C0 Ts0 = TT at hO
  cases hO with
  | absent h1 h2 =>
    simp only [Ty.cls.injEq] at hTT
    have ek := Declared.unique hwf hk h1 (by rw [hkn]; exact hTT.1)
    subst ek
    exact absurd (List.mem_map_of_mem (f := Method.name) hkM) h2
  | @found Cx _ Dl _ _ _ _ _ Do T0x psx ex h1 h2 h3 h4 h5 h6 =>
    simp only [Ty.cls.injEq] at hTT
    have hs' : Scope d Cx Delta0 := hTT.1 ▸ hs
    have hdm := Scope.dom_unique hwf hs' h2
    rw [<- bind_dom (D1 := Delta0 ++ Do) (D2 := Dl ++ Do) (by rw [dom_append, dom_append, hdm])] at h5 h6
    rcases h1 with ⟨K2, hk2, hkn2, hkM2⟩
    have ek := Declared.unique hwf hk2 hk (by rw [hkn2, hkn]; exact hTT.1.symm)
    subst ek
    have eM := names_unique (Declared.namesNodup hwf hk) hkM2 hkM rfl
    simp only [Method.mk.injEq] at eM
    rcases eM with ⟨eM1, eM2, _, eM4, _⟩
    subst eM1 eM2 eM4
    have e1 := hTT.1
    have e2 := hTT.2
    subst e1 e2
    exact ⟨h4, h5, h6⟩

end Funnelling
