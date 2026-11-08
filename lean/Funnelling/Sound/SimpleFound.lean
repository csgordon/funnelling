import Funnelling.Sound.GSubT
import Funnelling.Sound.IfThen

open Funnelling.SoundSimp

namespace Funnelling.High

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
  cases ftvList_mem.mp h with
  | intro T hT =>
    simp only [vars, listMem_iff, List.mem_map] at hT
    cases hT.1 with
    | intro Y hY => rw [<- hY.2] at hT; have := hT.2; simp [Ty.ftv] at this; rw [this]; exact hY.1

theorem dec_override {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {D : Dec}
    (hD : Declared d (.dec D)) {M : Method} (hM : List.Mem M D.Ms) {D0 : Dec} (hD0 : Declared d (.dec D0))
    {Gs Ts0 : List Ty} (hl : Gs.length = D.bounds.length) (hs : Sub d [] (.cls D.C Gs) (.cls D0.C Ts0)) :
    exists Us, Ts0 = Ty.substList (bind D.bounds Gs) Us /\ OverrideOkM d (.cls D0.C Us) M /\
      forall X, List.Mem X (Ty.ftvList Us) -> List.Mem X (dom D.bounds) := by
  have hn := (sf_dec hwf hok hD).ndom
  have e : Gs = Ty.substList (bind D.bounds Gs) (vars (dom D.bounds)) :=
    (vars_subst hn (by rw [hl]; simp [dom])).symm
  rw [e] at hs
  cases Sub.inv_subst hd (Delta2 := D.bounds) (A := dom D.bounds) hs rfl (fun X hX => ftv_vars hX) with
  | intro T0 h0 =>
    cases Sub.cls_target h0.2.1 rfl with
    | intro C1 h1 => cases h1 with
      | intro U0 e0 =>
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
            have hv : vars (dom D.bounds) ++ vars (dom Dm) = vars (dom (D.bounds ++ Dm)) := by
              rw [dom_append, vars_append]
            refine OverrideOkM.dec hD hM (by simp [vars, dom]) rfl ?_ ?_
            . rw [hv, substList_bind_vars_id hcl.1]
            . rw [hv, substList_bind_vars_id hcl.2]
        . have hsup : (Ty.cls D.C' D.Ts).subst (bind D.bounds (vars (dom D.bounds))) = Ty.cls D.C' D.Ts := by
            simp only [Ty.subst]
            rw [substList_bind_vars_id (hd.supD D hD)]
          rw [hsup] at e3
          exact (hok D hD.dec_mem).2.2.2 M D0.C U0 hM e3.2

end Funnelling.High
