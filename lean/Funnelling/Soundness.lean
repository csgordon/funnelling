import Funnelling.Sound.Soundness
import Funnelling.Sound.Determinism

namespace Funnelling

theorem typeSoundness {d e0 e T} (hwf : WFDecls d) (hok : DeclsOk d) (he0 : WFExpr e0)
    (ht : Typing d [] [] e0 T) (hs : Steps d e0 e) :
    Typing d [] [] e T /\ (IsValue e \/ exists e', Reduces d e e') := by
  induction hs with
  | refl => exact And.intro ht (progress hwf hok he0 ht)
  | step h1 _ ih => exact ih h1.2 (preservation hwf hok he0 ht h1)

theorem determinism {d e e1 e2} (hwf : WFDecls d) (he : WFExpr e) (h1 : Reduces d e e1)
    (h2 : Reduces d e e2) : Fresh e1 e2 := by
  rcases Step.toBase h1.1 with ⟨E, h⟩
  rcases h with ⟨a, h⟩
  rcases h with ⟨a', h⟩
  have hb := h.2.2
  have hna : NonValue a := Step.not_value hb.toStep
  have h2s := h2.1
  rw [h.1] at h2s he
  rcases Step.decomp h2s hna with ⟨a2, h3⟩
  have hb2 := Step.strip h3.1 hb
  have hw1 : WFExpr a' := by have := h1.2; rw [h.2.1] at this; exact WFExpr.plug this
  have hw2 : WFExpr a2 := by have := h2.2; rw [h3.2] at this; exact WFExpr.plug this
  rw [h.2.1, h3.2]
  exact Fresh.plug (det_base hwf (WFExpr.plug he) hw1 hw2 hb hb2 rfl) E

end Funnelling
