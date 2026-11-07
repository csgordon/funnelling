import Funnelling.High.Reduction
import Funnelling.Low.Soundness
import Funnelling.Translation

/-!
The formalization has two levels.
`Funnelling.High` follows the metarules of the paper as closely as possible; the appendix of the
paper compares it with the paper, rule by rule.
`Funnelling.Low` is free: its datatypes, functions and rules can change in any way that makes the
proofs easier (other binder representations, algorithmic typing, other judgements), and several
low levels can be tried.
The whole point is to keep the freedom of changing the low level without having to impact the
high level.
The only fixed statement is `Funnelling.High.typeSoundness` in `Funnelling.Soundness`, the Type
Soundness theorem of the paper; it must be proved with no `sorry` and no new axiom.
Everything else is a component of its proof and can change: the low level, the translation in
`Funnelling.Translation`, the lemmas of this file and their statements, and `Funnelling.Proof`.

`Funnelling.Proof` currently splits Type Soundness into progress and preservation on the high
level, and proves each of them through the low level with the lemmas of this file.
That is one option, not a requirement.
Another option applies the translation first: state Type Soundness on the low level, split it
there into progress and preservation, and transport the whole statement back through a
simulation between the two reductions.
Any other proof structure is equally acceptable, as long as `Funnelling.High.typeSoundness`
keeps its statement.
-/

namespace Funnelling

theorem isValue_tr {e : High.Expr} : High.IsValue e <-> (trExpr e).isValue = true := by
  sorry

theorem wfExpr_tr {e : High.Expr} (he : High.WFExpr e) : Low.wfExpr (trExpr e) = true := by
  sorry

theorem declsOk_tr {d : High.Decls} (hwf : High.WFDecls d) (hok : High.DeclsOk d .funnelled) :
    Low.DeclsOk (trDecls d) := by
  sorry

theorem typing_tr {d : High.Decls} {e : High.Expr} {T : High.Ty} (hwf : High.WFDecls d) :
    High.Typing d .funnelled [] [] e T <->
      Low.Typing (trDecls d) false [] [] (trExpr e) (trTy T) := by
  sorry

theorem step_tr {d : High.Decls} {e e' : High.Expr} (hwf : High.WFDecls d) (he : High.WFExpr e)
    (hs : High.Reduces d e e') : Low.Step (trDecls d) (trExpr e) (trExpr e') := by
  sorry

theorem step_back {d : High.Decls} {e : High.Expr} {e'' : Low.Expr} (hwf : High.WFDecls d)
    (he : High.WFExpr e) (hs : Low.Step (trDecls d) (trExpr e) e'') :
    exists e', High.Reduces d e e' := by
  sorry

end Funnelling
