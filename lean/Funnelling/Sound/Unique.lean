import Funnelling.Sound.ScopeFacts

open Funnelling.SoundSimp

namespace Funnelling.High

theorem superChain_stab {d : Decls} : forall (n : Nat) (C : ClassName),
    (exists D0, List.Mem D0 (superChain d n C) /\ D0.C = Object) -> superChain d (n + 1) C = superChain d n C
  | 0, C, h => by cases h with | intro D0 h => simp [superChain] at h
  | n + 1, C, h => by
    cases hf : findDec d C with
    | none => simp [superChain, hf]
    | some D =>
      have hDC : D.C = C := by
        have := (find_some hf).2
        simpa using this
      by_cases ho : C = Object
      . simp [superChain, hf, ho]
      . have h1 : superChain d (n + 2) C = D :: superChain d (n + 1) D.C' := by simp [superChain, hf, ho]
        have h2 : superChain d (n + 1) C = D :: superChain d n D.C' := by simp [superChain, hf, ho]
        rw [h1, h2]
        rw [h2] at h
        have h' : exists D0, List.Mem D0 (superChain d n D.C') /\ D0.C = Object := by
          rcases h with ⟨D0, hD0⟩
          refine Exists.intro D0 (And.intro ?_ hD0.2)
          cases hD0.1 with
          | head => rw [hDC] at hD0; exact absurd hD0.2 ho
          | tail _ h => exact h
        rw [superChain_stab n D.C' h']

def rank (d : Decls) (C : ClassName) : Nat := (superChain d (d.length + 1) C).length

theorem rank_super {d : Decls} (hwf : WFDecls d) {D : Dec} (hD : Declared d (.dec D)) (ho : Not (D.C = Object)) :
    rank d D.C = rank d D.C' + 1 := by
  have hf := findDec_self hwf hD.dec_mem
  have h1 : superChain d (d.length + 1) D.C = D :: superChain d d.length D.C' := by simp [superChain, hf, ho]
  have hA9 := hwf.2.2.2.2.2.2.2.2.1.2 D hD.dec_mem
  rw [h1] at hA9
  have h' : exists D0, List.Mem D0 (superChain d d.length D.C') /\ D0.C = Object := by
    rcases hA9 with ⟨D0, hD0⟩
    refine Exists.intro D0 (And.intro ?_ hD0.2)
    cases hD0.1 with
    | head => exact absurd hD0.2 ho
    | tail _ h => exact h
  simp only [rank]
  rw [h1, superChain_stab d.length D.C' h']
  simp

theorem rank_sub {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} (hD : Declared d (.dec D))
    {Ts : List Ty} {C2 : ClassName} {U : List Ty} (h : Sub d Delta (.cls D.C Ts) (.cls C2 U)) :
    rank d C2 <= rank d D.C := by
  generalize he : Ty.cls D.C Ts = T at h
  generalize ht : Ty.cls C2 U = T' at h
  induction h generalizing D Ts with
  | subRefl =>
    rw [<- ht] at he
    simp only [Ty.cls.injEq] at he
    rw [he.1]; exact Nat.le_refl _
  | @subInherit D' Ts0' T' hD' hl _ ih =>
    simp only [Ty.cls.injEq] at he
    have e := K.dec.inj (Declared.unique hwf hD' hD he.1.symm)
    subst e
    rcases Declared.super hwf hD' with ⟨D'', hD''⟩
    have hsup := hD''.2
    simp only [K.sup] at hsup
    have r := ih hD''.1 (Ts := Ty.substList (bind D'.bounds Ts0') D'.Ts) (by simp only [Ty.subst]; rw [hsup]) ht
    rw [hsup] at r
    by_cases ho : D'.C = Object
    . have ho2 := (object_unique hwf hD' ho).1
      rw [ho2, <- ho] at r
      exact r
    . rw [rank_super hwf hD' ho]; exact Nat.le_succ_of_le r
  | subInheritLocal hD' _ _ =>
    simp only [Ty.cls.injEq] at he
    exact absurd (Declared.dec_loc hwf hD hD' he.1) id
  | subVar => cases he

theorem no_cycle {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} (hD : Declared d (.dec D))
    (ho : Not (D.C = Object)) {Ts U : List Ty} (hl : Ts.length = D.bounds.length)
    (h : Sub d Delta ((Ty.cls D.C' D.Ts).subst (bind D.bounds Ts)) (.cls D.C U)) : False := by
  rcases Declared.super hwf hD with ⟨D'', hD''⟩
  have hsup := hD''.2
  simp only [K.sup] at hsup
  simp only [Ty.subst] at h
  rw [<- hsup] at h
  have r := rank_sub hwf hD''.1 h
  rw [rank_super hwf hD ho, hsup] at r
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) r)

theorem object_args {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {U0 U : List Ty}
    (h : Sub d Delta (.cls Object U0) (.cls Object U)) : U = U0 \/ U = [] := by
  generalize he : Ty.cls Object U0 = T at h
  generalize ht : Ty.cls Object U = T' at h
  induction h generalizing U0 with
  | subRefl => rw [<- ht] at he; simp only [Ty.cls.injEq] at he; exact Or.inl he.2.symm
  | @subInherit D Ts0 T' hD hl _ ih =>
    simp only [Ty.cls.injEq] at he
    have ho := object_unique hwf hD he.1.symm
    rcases ih (U0 := Ty.substList (bind D.bounds Ts0) D.Ts) (by simp only [Ty.subst]; rw [ho.1]) ht with e | e
    . right; rw [e, ho.2]; rfl
    . exact Or.inr e
  | subInheritLocal hD _ _ =>
    simp only [Ty.cls.injEq] at he
    rcases object_declared hwf with ⟨D0, hD0⟩; exact absurd (Declared.dec_loc hwf hD0.1 hD (by rw [hD0.2.1, he.1])) id
  | subVar => cases he

theorem object_bounds {d : Decls} (hwf : WFDecls d) {D : Dec} (hD : Declared d (.dec D)) (ho : D.C = Object) :
    D.bounds = [] := by
  rcases object_declared hwf with ⟨D0, hD0⟩
  have e := K.dec.inj (Declared.unique hwf hD hD0.1 (by show D.C = D0.C; rw [ho, hD0.2.1]))
  rw [e]; exact hD0.2.2.1

theorem sub_unique_dec {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {T1 : Ty}
    (h1 : exists D Ts, Declared d (.dec D) /\ T1 = .cls D.C Ts) {C' : ClassName} {U1 : List Ty}
    (hs1 : Sub d Delta T1 (.cls C' U1)) : forall {U2 : List Ty}, Sub d Delta T1 (.cls C' U2) -> U1 = U2 := by
  generalize ht : Ty.cls C' U1 = T' at hs1
  induction hs1 with
  | @subRefl T =>
    intro U2 hs2
    cases h1 with
    | intro D h1 => cases h1 with
      | intro Ts h1 =>
        rw [h1.2] at ht hs2
        simp only [Ty.cls.injEq] at ht
        rcases Sub.dec_step hwf h1.1 hs2 with e | hs3
        . simp only [Ty.cls.injEq] at e; rw [ht.2, e.2]
        . have hC : C' = D.C := ht.1
          rw [hC] at hs3
          by_cases ho : D.C = Object
          . have hb := object_bounds hwf h1.1 ho
            have hU : Ts = [] := by have := hs3.1; rw [hb] at this; cases Ts <;> simp_all
            have hs4 := hs3.2
            simp only [Ty.subst] at hs4
            rw [(object_unique hwf h1.1 ho).1, (object_unique hwf h1.1 ho).2, ho] at hs4
            simp only [Ty.substList] at hs4
            rw [ht.2, hU]
            rcases object_args hwf hs4 with e | e
            . exact e.symm
            . exact e.symm
          . exact absurd (no_cycle hwf h1.1 ho hs3.1 hs3.2) id
  | @subInherit D Ts0 T' hD hl hs ih =>
    intro U2 hs2
    rcases Sub.dec_step hwf hD hs2 with e | hs3
    . rw [<- ht] at hs
      simp only [Ty.cls.injEq] at e
      have hC : C' = D.C := e.1
      rw [hC] at hs
      by_cases ho : D.C = Object
      . have hb := object_bounds hwf hD ho
        have hT0 : Ts0 = [] := by rw [hb] at hl; cases Ts0 <;> simp_all
        simp only [Ty.subst] at hs
        rw [(object_unique hwf hD ho).1, (object_unique hwf hD ho).2, ho] at hs
        simp only [Ty.substList] at hs
        rw [e.2, hT0]
        rcases object_args hwf hs with e2 | e2
        . exact e2
        . exact e2
      . exact absurd (no_cycle hwf hD ho hl hs) id
    . refine ih ?_ ht hs3.2
      rcases Declared.super hwf hD with ⟨D'', hD''⟩
      refine Exists.intro D'' (Exists.intro (Ty.substList (bind D.bounds Ts0) D.Ts) (And.intro hD''.1 ?_))
      simp only [Ty.subst]
      rw [hD''.2]; rfl
  | subInheritLocal hD _ _ =>
    intro _ _
    cases h1 with
    | intro D h1 => cases h1 with
      | intro Ts h1 =>
        simp only [Ty.cls.injEq] at h1
        exact absurd (Declared.dec_loc hwf h1.1 hD h1.2.1.symm) id
  | subVar =>
    intro _ _
    cases h1 with
    | intro D h1 => cases h1 with
      | intro Ts h1 => cases h1.2

end Funnelling.High