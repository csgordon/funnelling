import Funnelling.Sound.WFStep

open Funnelling.SoundSimp

namespace Funnelling.High

theorem preservationH {d : Decls} {e e' : Expr} {T : Ty} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (ht : Typing d [] [] e T) (hs : Reduces d e e') : Typing d [] [] e' T := by
  rcases Step.toBase hs.1 with ⟨E, h⟩
  rcases h with ⟨a, h⟩
  rcases h with ⟨a', h⟩
  rw [h.1] at ht he
  have hw' := hs.2
  rw [h.2.1] at hw' |-
  cases typing_plug E ht with
  | intro Ta hTa => exact hTa.2 a' (presBase' hwf hok (WFExpr.plug he) (WFExpr.plug hw') h.2.2 hTa.1)

theorem progressH {d : Decls} {e : Expr} {T : Ty} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (ht : Typing d [] [] e T) : IsValue e \/ exists e', Reduces d e e' := by
  rcases progress_step hwf hok he ht with hv | ⟨e', hs⟩
  . exact Or.inl hv
  . exact Or.inr (wf_step hwf hok he hs)

theorem typeSoundnessH {d e0 e T} (hwf : WFDecls d) (hok : DeclsOk d) (he0 : WFExpr e0)
    (ht : Typing d [] [] e0 T) (hs : Steps d e0 e) :
    Typing d [] [] e T /\ (IsValue e \/ exists e', Reduces d e e') := by
  induction hs with
  | refl => exact And.intro ht (progressH hwf hok he0 ht)
  | step h1 _ ih => exact ih h1.2 (preservationH hwf hok he0 ht h1)

end Funnelling.High