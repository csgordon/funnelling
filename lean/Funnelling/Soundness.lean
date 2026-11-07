import Funnelling.Proof

namespace Funnelling.High

theorem typeSoundness {d e0 e T} (hwf : WFDecls d) (hok : DeclsOk d .funnelled) (he0 : WFExpr e0)
    (ht : Typing d .funnelled [] [] e0 T) (hs : Steps d e0 e) :
    Typing d .funnelled [] [] e T /\ (IsValue e \/ exists e', Reduces d e e') :=
  Proof.typeSoundness hwf hok he0 ht hs

end Funnelling.High
