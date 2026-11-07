import Funnelling.Adequacy
import Funnelling.Sound.Determinism

namespace Funnelling.Proof

open Funnelling.High

theorem progress {d e T} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (ht : Typing d [] [] e T) : IsValue e \/ exists e', Reduces d e e' :=
  match Low.progress (declsOk_tr hwf hok) (wfExpr_tr he) ((typing_tr hwf).mp ht) with
  | Or.inl hv => Or.inl (isValue_tr.mpr hv)
  | Or.inr (Exists.intro _ hs) => Or.inr (step_back hwf he hs)

theorem preservation {d e e' T} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (ht : Typing d [] [] e T) (hs : Reduces d e e') : Typing d [] [] e' T :=
  (typing_tr hwf).mpr
    (Low.preservation (declsOk_tr hwf hok) (wfExpr_tr he) ((typing_tr hwf).mp ht) (step_tr hwf he hs))

theorem typeSoundness {d e0 e T} (hwf : WFDecls d) (hok : DeclsOk d) (he0 : WFExpr e0)
    (ht : Typing d [] [] e0 T) (hs : Steps d e0 e) :
    Typing d [] [] e T /\ (IsValue e \/ exists e', Reduces d e e') := by
  induction hs with
  | refl => exact And.intro ht (progress hwf hok he0 ht)
  | step h1 _ ih => exact ih h1.2 (preservation hwf hok he0 ht h1)

theorem determinism {d e e1 e2} (hwf : WFDecls d) (he : WFExpr e) (h1 : Reduces d e e1)
    (h2 : Reduces d e e2) : Fresh e1 e2 :=
  determinismHigh hwf he h1 h2

end Funnelling.Proof
