import Funnelling.Sound.Soundness

namespace Funnelling.Proof

open Funnelling.High

theorem typeSoundness {d e0 e T} (hwf : WFDecls d) (hok : DeclsOk d) (he0 : WFExpr e0)
    (ht : Typing d [] [] e0 T) (hs : Steps d e0 e) :
    Typing d [] [] e T /\ (IsValue e \/ exists e', Reduces d e e') :=
  typeSoundnessH hwf hok he0 ht hs

theorem determinism {d e e1 e2} (hwf : WFDecls d) (he : WFExpr e) (h1 : Reduces d e e1)
    (h2 : Reduces d e e2) : Fresh e1 e2 :=
  determinismHigh hwf he h1 h2

end Funnelling.Proof
