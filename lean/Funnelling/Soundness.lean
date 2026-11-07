import Funnelling.Reduction
import Funnelling.WellFormed

namespace Funnelling

def DeclsOk (d : Decls) : Prop := wfDecls d = true /\ forall dec, List.Mem dec d -> ClassOk d false dec

theorem stepWellFormed {d e e' t} (hd : DeclsOk d) (he : wfExpr e = true)
    (ht : Typing d false [] [] e t) (hs : Step d e e') : wfExpr e' = true := by
  sorry

theorem progress {d e t} (hd : DeclsOk d) (he : wfExpr e = true)
    (ht : Typing d false [] [] e t) :
    e.isValue = true \/ exists e', Step d e e' := by
  sorry

theorem preservation {d e e' t} (hd : DeclsOk d) (he : wfExpr e = true)
    (ht : Typing d false [] [] e t) (hs : Step d e e') : Typing d false [] [] e' t := by
  sorry

theorem typeSoundness {d e0 e t} (hd : DeclsOk d) (he0 : wfExpr e0 = true)
    (ht : Typing d false [] [] e0 t) (hs : Steps d e0 e) :
    Typing d false [] [] e t /\ (e.isValue = true \/ exists e', Step d e e') := by
  induction hs with
  | refl => exact And.intro ht (progress hd he0 ht)
  | step h1 _ ih => exact ih (stepWellFormed hd he0 ht h1) (preservation hd he0 ht h1)

end Funnelling
