import Funnelling.Adequacy

namespace Funnelling.Proof

open Funnelling.High

theorem progress {d e T} (hwf : WFDecls d) (hok : DeclsOk d .funnelled) (he : WFExpr e)
    (ht : Typing d .funnelled [] [] e T) : IsValue e \/ exists e', Reduces d e e' :=
  match Low.progress (declsOk_tr hwf hok) (wfExpr_tr he) ((typing_tr hwf).mp ht) with
  | Or.inl hv => Or.inl (isValue_tr.mpr hv)
  | Or.inr (Exists.intro _ hs) => Or.inr (step_back hwf he hs)

theorem preservation {d e e' T} (hwf : WFDecls d) (hok : DeclsOk d .funnelled) (he : WFExpr e)
    (ht : Typing d .funnelled [] [] e T) (hs : Reduces d e e') : Typing d .funnelled [] [] e' T :=
  (typing_tr hwf).mpr
    (Low.preservation (declsOk_tr hwf hok) (wfExpr_tr he) ((typing_tr hwf).mp ht) (step_tr hwf he hs))

theorem typeSoundness {d e0 e T} (hwf : WFDecls d) (hok : DeclsOk d .funnelled) (he0 : WFExpr e0)
    (ht : Typing d .funnelled [] [] e0 T) (hs : Steps d e0 e) :
    Typing d .funnelled [] [] e T /\ (IsValue e \/ exists e', Reduces d e e') := by
  induction hs with
  | refl => exact And.intro ht (progress hwf hok he0 ht)
  | step h1 _ ih => exact ih h1.2 (preservation hwf hok he0 ht h1)

end Funnelling.Proof
