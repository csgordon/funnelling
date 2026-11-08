import Funnelling.Sound.WellFormedStep

open Funnelling.SoundSimp

namespace Funnelling

theorem preservation {d : Decls} {e e' : Expr} {T : Ty} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (ht : Typing d [] [] e T) (hs : Reduces d e e') : Typing d [] [] e' T := by
  obtain ⟨E, a, a', rfl, rfl, hb⟩ := Step.toBase hs.1
  obtain ⟨Ta, hTa, hE⟩ := typing_plug E ht
  exact hE a' (preservationBase hwf hok (WFExpr.plug he) (WFExpr.plug hs.2) hb hTa)

theorem progress {d : Decls} {e : Expr} {T : Ty} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (ht : Typing d [] [] e T) : IsValue e \/ exists e', Reduces d e e' := by
  rcases progress_step hwf hok he ht with hv | ⟨e', hs⟩
  . exact Or.inl hv
  . exact Or.inr (wf_step hwf hok he hs)

end Funnelling