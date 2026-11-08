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
    {Gs Ts0 : List Ty} (hl : Gs.length = D.bounds.length) (hs : Sub d [] (.cls D.C Gs) (.cls D0.C Ts0)) :
    exists Us, Ts0 = Ty.substList (bind D.bounds Gs) Us /\ OverrideOkM d (.cls D0.C Us) M /\
      forall X, List.Mem X (Ty.ftvList Us) -> List.Mem X (dom D.bounds) := by
  have hn := (sf_dec hwf hok hD).ndom
  have e : Gs = Ty.substList (bind D.bounds Gs) (vars (dom D.bounds)) :=
    (vars_subst hn (by rw [hl]; simp [dom])).symm
  rw [e] at hs
  rcases Sub.inv_subst hd (Delta2 := D.bounds) (A := dom D.bounds) hs rfl (fun X hX => ftv_vars hX) with ⟨T0, h0⟩
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
      have hcl := declMeth_closed hwf hok hD hM
      simp only [K.gvars, <- dom_append] at hcl
      have hv : vars (dom D.bounds) ++ vars (dom Dm) = vars (dom (D.bounds ++ Dm)) := by rw [dom_append, vars_append]
      refine OverrideOkM.dec hD hM (by simp [vars, dom]) rfl ?_ ?_
      . rw [hv, substList_bind_vars_id hcl.1]
      . rw [hv, substList_bind_vars_id hcl.2]
  . have hsup : (Ty.cls D.C' D.Ts).subst (bind D.bounds (vars (dom D.bounds))) = Ty.cls D.C' D.Ts := by
      simp only [Ty.subst]
      rw [substList_bind_vars_id (hd.supD D hD)]
    rw [hsup] at e3
    exact (hok D hD.dec_mem).2.2.2 M D0.C U0 hM e3.2

theorem bind_append_len {Dl1 Dl2 : Bounds} {as bs : List Ty} (h : as.length = Dl1.length) :
    bind (Dl1 ++ Dl2) (as ++ bs) = bind Dl1 as ++ bind Dl2 bs := by
  simp only [bind, dom_append]
  rw [List.zip_append (by simp [h, dom])]

theorem found_sig {d : Decls} (hwf : WFDecls d) {C0 : ClassName} {Ts0 : List Ty} {Delta0 : Bounds} {Ts2 : List Ty}
    {Delta1 : Bounds} {T0c : Ty} {m : MethName} {psc : List VarDecl} {body : Expr} {Dp : Bounds} {T0 : Ty}
    {ps : List VarDecl} {e : Expr} (hs : Scope d (.cls C0 Ts0) Delta0 Ts2)
    (hm : MethodIn d (.mk Delta1 T0c m psc body) C0) (hl2 : Ts2.length = Delta0.length)
    (hO : OverrideOkM d (.cls C0 Ts0) (.mk Dp T0 m ps e)) :
    Ts2 = Ts0 /\ Dp.length = Delta1.length /\
      Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ vars (dom Dp))) (cod Delta1) = cod Dp /\
      Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ vars (dom Dp))) (T0c :: psc.map VarDecl.T) =
        T0 :: ps.map VarDecl.T := by
  rcases hm with ⟨k, hk, hkn, hkM⟩
  generalize hTT : Ty.cls C0 Ts0 = TT at hO
  cases hO with
  | absent h1 h2 =>
    simp only [Ty.cls.injEq] at hTT
    have ek := Declared.unique hwf hk h1 (by rw [hkn]; exact hTT.1)
    subst ek
    exact absurd (List.mem_map_of_mem (f := Method.name) hkM) h2
  | @dec D2 _ _ _ _ _ _ Do T0x psx ex h1 h2 h3 h4 h5 h6 =>
    simp only [Ty.cls.injEq] at hTT
    have ek := Declared.unique hwf hk h1 (by rw [hkn]; exact hTT.1)
    subst ek
    have eM := names_unique (Declared.namesNodup hwf h1) h2 hkM rfl
    simp only [Method.mk.injEq] at eM
    rcases eM with ⟨eM1, eM2, _, eM4, _⟩
    subst eM1 eM2 eM4
    have e1 := hTT.1
    have e2 := hTT.2
    subst e1 e2
    have es := Scope.dec_eq hwf h1 hs
    rcases es with ⟨es1, es2⟩
    subst es1 es2
    exact And.intro rfl (And.intro h4 (And.intro h5 h6))
  | @loc C1 Fs C1' Ts1' es1 Ms1 _ _ _ _ _ _ Do T0x psx ex h1 h2 h3 h4 h5 h6 =>
    simp only [Ty.cls.injEq] at hTT
    have ek := Declared.unique hwf hk h1 (by rw [hkn]; exact hTT.1)
    subst ek
    have eM := names_unique (Declared.namesNodup hwf h1) h2 hkM rfl
    simp only [Method.mk.injEq] at eM
    rcases eM with ⟨eM1, eM2, _, eM4, _⟩
    subst eM1 eM2 eM4
    have e1 := hTT.1
    have e2 := hTT.2
    subst e1 e2
    rcases Scope.loc_declared hs with hsd | hsd
    . rcases hsd with ⟨D, hD, hDC, _⟩
      exact absurd (Declared.dec_loc hwf hD h1 hDC) id
    . rcases hsd with ⟨Fs2, C2, Ts2', es2, Ms2, Delta, hdecl, hpair⟩
      have eK := Declared.unique hwf hdecl h1 rfl
      simp only [K.loc.injEq] at eK
      rcases eK with ⟨_, eF, _⟩
      subst eF
      have hall : forall F, List.Mem F Fs2 -> F.isFunnel = true := fun F hF => hwf.2.2.2.2.2.2.2.2.2.2 _ h1.mem F hF
      have eT := pairing_funnels hpair hall
      subst eT
      have hb := bind_eq_bindF (Pairing.dom_eq hpair) hall Ts2
      refine And.intro rfl (And.intro h4 (And.intro ?_ ?_))
      . rw [bind_append_len hl2, hb]; exact h5
      . rw [bind_append_len hl2, hb]; exact h6

end Funnelling
