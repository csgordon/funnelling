import Funnelling.Sound.Progress

open Funnelling.SoundSimp

namespace Funnelling.High

theorem wf_base {d : Decls} {a a' : Expr} (hwf : WFDecls d) (hok : DeclsOk d) (ha : WFExpr a)
    (hs : BaseStep d a a') : exists a'', BaseStep d a a'' /\ WFExpr a'' := by
  sorry

theorem WFExpr.replace {E : ECtx} {a a' : Expr} (h : WFExpr (E.plug a)) (h' : WFExpr a') :
    WFExpr (E.plug a') := by
  sorry

theorem wf_step {d : Decls} {e e' : Expr} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (hs : Step d e e') : exists e'', Reduces d e e'' := by
  rcases Step.toBase hs with ⟨E, a, a', hE, _, hb⟩
  subst hE
  rcases wf_base hwf hok (WFExpr.plug he) hb with ⟨a'', hb'', hw''⟩
  exact ⟨E.plug a'', Step.ctx hb''.toStep, WFExpr.replace he hw''⟩

end Funnelling.High
