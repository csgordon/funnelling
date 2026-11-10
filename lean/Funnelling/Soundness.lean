import Funnelling.Sound.Soundness

namespace Funnelling

theorem typeSoundness {d e0 e T} (hwf : WFDecls d) (hok : DeclsOk d) (he0 : WFExpr e0)
    (ht : Typing d [] [] e0 T) (hs : ReducesStar d e0 e) :
    Typing d [] [] e T /\ (IsValue e \/ exists e', Reduces d e e') := by
  induction hs with
  | refl => exact And.intro ht (progress hwf hok he0 ht)
  | step h1 _ ih => exact ih h1.2 (preservation hwf hok he0 ht h1)

theorem determinism {d e e1 e2} (hwf : WFDecls d) (he : WFExpr e) (h1 : Reduces d e e1)
    (h2 : Reduces d e e2) : Fresh e1 e2 := by
  obtain ⟨E, a, a', rfl, rfl, hb⟩ := Step.toBase h1.1
  obtain ⟨a2, h2a, rfl⟩ := Step.decomp h2.1 (Step.not_value hb.toStep)
  exact Fresh.plug (det_base hwf (WFExpr.plug he) (WFExpr.plug h1.2) (WFExpr.plug h2.2) hb (Step.strip h2a hb) rfl) E

end Funnelling
