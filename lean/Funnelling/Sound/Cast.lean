import Funnelling.Sound.Types

open Funnelling.SoundSimp

namespace Funnelling.High

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
    . cases h' with
      | intro X' hX =>
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

end Funnelling.High