import Funnelling.Sound.Cast

open Funnelling.SoundSimp

namespace Funnelling.High

theorem Sub.dec_step {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} (hD : Declared d (.dec D))
    {Ts : List Ty} {T : Ty} (h : Sub d Delta (.cls D.C Ts) T) :
    T = .cls D.C Ts \/ (Ts.length = D.bounds.length /\ Sub d Delta ((Ty.cls D.C' D.Ts).subst (bind D.bounds Ts)) T) := by
  generalize he : Ty.cls D.C Ts = T0 at h
  cases h with
  | subRefl => exact Or.inl rfl
  | @subInherit D' Ts0 T' hD' hl h' =>
    simp only [Ty.cls.injEq] at he
    have e := Declared.unique hwf hD' hD he.1.symm
    cases e
    rw [he.2]
    exact Or.inr (And.intro hl h')
  | subInheritLocal hD' _ _ =>
    simp only [Ty.cls.injEq] at he
    exact absurd (Declared.dec_loc hwf hD hD' he.1) id
  | subVar => cases he

theorem Sub.loc_step {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {C Fs C' Ts' es Ms}
    (hD : Declared d (.loc C Fs C' Ts' es Ms)) {Ts : List Ty} {T : Ty} (h : Sub d Delta (.cls C Ts) T) :
    T = .cls C Ts \/ (Ts.length = Fs.length /\ Sub d Delta ((Ty.cls C' Ts').subst (bindF Fs Ts)) T) := by
  generalize he : Ty.cls C Ts = T0 at h
  cases h with
  | subRefl => exact Or.inl rfl
  | subInherit hD' _ _ =>
    simp only [Ty.cls.injEq] at he
    exact absurd (Declared.dec_loc hwf hD' hD he.1.symm) id
  | @subInheritLocal C2 Fs2 C2' Ts2' es2 Ms2 Ts2 T' hD' hl h' =>
    simp only [Ty.cls.injEq] at he
    have e := Declared.unique hwf hD' hD he.1.symm
    cases e
    rw [he.2]
    exact Or.inr (And.intro hl h')
  | subVar => cases he

theorem Scope.loc_declared {d : Decls} {Delta0 : Bounds} {Ts0 : List Ty} {C0 : ClassName} {Ts : List Ty}
    (h : Scope d (.cls C0 Ts) Delta0 Ts0) :
    (exists D, Declared d (.dec D) /\ D.C = C0 /\ Delta0 = D.bounds /\ Ts0 = Ts) \/
    (exists Fs C' Ts' es Ms Delta, Declared d (.loc C0 Fs C' Ts' es Ms) /\ Pairing Delta Fs Ts Delta0 Ts0) := by
  generalize he : Ty.cls C0 Ts = T at h
  cases h with
  | @dec D Ts2 hD =>
    simp only [Ty.cls.injEq] at he
    exact Or.inl (Exists.intro D (And.intro hD (And.intro he.1.symm (And.intro rfl he.2.symm))))
  | @loc C Delta' T0 m ps e C1 Fs C' Ts' es Ms T Delta Ts'' Ts2 Delta0 Ts0 h1 h2 h3 h4 h5 =>
    simp only [Ty.cls.injEq] at he
    rcases h1 with ⟨k, hk⟩
    have hd := Declared.loc hk.1 (by rw [hk.2.1] at hk; exact hk.2.2) h2
    rw [he.1, he.2] at *
    exact Or.inr (Exists.intro Fs (Exists.intro C' (Exists.intro Ts' (Exists.intro es (Exists.intro Ms
      (Exists.intro _ (And.intro hd h5)))))))

theorem Scope.dec_eq {d : Decls} (hwf : WFDecls d) {D : Dec} (hD : Declared d (.dec D)) {Ts Ts0 : List Ty}
    {Delta0 : Bounds} (h : Scope d (.cls D.C Ts) Delta0 Ts0) : Delta0 = D.bounds /\ Ts0 = Ts := by
  rcases h.loc_declared with h' | h'
  . rcases h' with ⟨D', h'⟩
    have e := Declared.unique hwf h'.1 hD h'.2.1
    cases e
    exact h'.2.2
  . rcases h' with ⟨Fs, C', Ts', es, Ms, Delta, h'⟩
    exact absurd (Declared.dec_loc hwf hD h'.1 rfl) id

theorem find_some {A : Type} {p : A -> Bool} : forall {l : List A} {x : A}, l.find? p = some x ->
    List.Mem x l /\ p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    by_cases ha : p a = true
    . rw [List.find?_cons_of_pos ha] at h
      cases h
      exact And.intro (List.Mem.head _) ha
    . rw [List.find?_cons_of_neg ha] at h
      have r := find_some h
      exact And.intro (List.Mem.tail _ r.1) r.2

theorem Declared.super {d : Decls} (hwf : WFDecls d) {k : K} (hk : Declared d k) :
    exists D', Declared d (.dec D') /\ D'.C = k.sup := by
  have h := hwf.2.2.2.2.2.2.2.2.2.1 k hk.mem
  cases hf : findDec d k.sup with
  | none => rw [hf] at h; cases h
  | some D' =>
    have r := find_some hf
    exact Exists.intro D' (And.intro (Declared.dec r.1) (by simpa using r.2))

theorem pairing_ground_nil {Delta : Bounds} : forall {Gs : List GTy} {Ts : List Ty} {Delta' : Bounds} {Ts'' : List Ty},
    Pairing Delta (Gs.map Funnel.ground) Ts Delta' Ts'' -> Delta' = []
  | [], _, _, _, h => by cases h; rfl
  | G :: Gs, _, _, _, h => by
    cases h with
    | ground h => exact pairing_ground_nil h

theorem abs_ground {Gs : List GTy} : abs (Gs.map Funnel.ground) = GTy.tys Gs := by
  rw [GTy.tys_eq_map]
  simp [abs, List.map_map, Function.comp_def, Funnel.abs]

end Funnelling.High