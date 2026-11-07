import Funnelling.Sound.PresEasy

open Funnelling.SoundSimp

namespace Funnelling.High

theorem declOk {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) : DeclOk d := by
  sorry

theorem pres_fieldFound {d : Decls} (hwf : WFDecls d) {D : Dec} {f : FieldName} {Gs : List GTy}
    {vs1 vs : List Value} {v : Value} {T : Ty} (hD : Declared d (.dec D)) (hl : vs1.length = D.Ss.length)
    (hm : List.Mem (f, v) ((D.Ss.map Slot.f).zip vs1))
    (h : Typing d [] [] (.field (Value.new D.C Gs (vs1 ++ vs)).expr f) T) : Typing d [] [] v.expr T := by
  sorry

theorem pres_ifThen {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {C' : ClassName} {Ts Ts' : List Ty}
    {x : VarName} {e1 e1' e2 : Expr} {v : Value} {T : Ty} (hs : Sub d [] (typeOf v) (.cls C' Ts'))
    (hf : Fresh e1 e1') (hd : VSubstDefined [x] e1') (ha : WFExpr (.ifInst v.expr (.cls C' Ts) x e1 e2))
    (ha' : WFExpr (e1'.vsubst [(x, v)])) (h : Typing d [] [] (.ifInst v.expr (.cls C' Ts) x e1 e2) T) :
    Typing d [] [] (e1'.vsubst [(x, v)]) T := by
  sorry

theorem pres_simpleFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {D : Dec} {M : Method} {m : MethName}
    {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value} {Gs Gs' : List GTy}
    {vs : List Value} {T : Ty} (hD : Declared d (.dec D)) (hM : List.Mem M D.Ms)
    (hF : FreshM M (.mk Delta' T0 m ps e0)) (hG : Gs.length = D.bounds.length) (hG' : Gs'.length = Delta'.length)
    (hN : (dom D.bounds ++ dom Delta').Nodup) (hN' : (this :: ps.map VarDecl.x).Nodup)
    (hp : ps.length = vs.length) (hgs : GSubstDefined (dom D.bounds ++ dom Delta') e0)
    (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0)
    (ha : WFExpr (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)))
    (ha' : WFExpr ((e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
      ((this :: ps.map VarDecl.x).zip (v0 :: vs))))
    (h : Typing d [] [] (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
      ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  sorry

theorem pres_innerFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {C C' : ClassName} {Ms : List Method}
    {M : Method} {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value}
    {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} {T : Ty} (hv : v0 = Value.newLocal C Gs C' Gs'' vs0 Ms)
    (hM : List.Mem M Ms) (hF : FreshM M (.mk Delta' T0 m ps e0)) (hG' : Gs'.length = Delta'.length)
    (hp : ps.length = vs.length) (hN : (dom Delta').Nodup) (hN' : (this :: ps.map VarDecl.x).Nodup)
    (hgs : GSubstDefined (dom Delta') e0) (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0)
    (ha : WFExpr (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)))
    (ha' : WFExpr ((e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))))
    (h : Typing d [] [] (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  sorry

theorem presBase' {d : Decls} {a a' : Expr} {T : Ty} (hwf : WFDecls d) (hok : DeclsOk d) (ha : WFExpr a)
    (ha' : WFExpr a') (hs : BaseStep d a a') (ht : Typing d [] [] a T) : Typing d [] [] a' T := by
  have hd := declOk hwf hok
  cases hs with
  | simpleFieldFound h1 h2 h3 => exact pres_fieldFound hwf h1 h2 h3 ht
  | simpleFieldSuper h1 h2 h3 h4 h5 => exact pres_simpleFieldSuper hwf h1 h2 h3 h4 ht
  | innerFieldSuper => exact pres_innerFieldSuper hwf ht
  | ifThen h1 h2 h3 => exact pres_ifThen hwf hok h1 h2 h3 ha ha' ht
  | ifElse h1 => exact pres_ifElse ht
  | simpleAddSuper h1 => exact pres_addSuper hwf h1 ht
  | simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    subst h11
    exact pres_simpleFound hwf hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ha ha' ht
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    subst h10
    exact pres_innerFound hwf hok h1 h2 h3 h4 h5 h6 h7 h8 h9 ha ha' ht
  | innerSuper h1 h2 => exact pres_innerSuper hwf h1 h2 ht
  | searchSuper h1 h2 h3 h4 => exact pres_searchSuper hwf hok hd h1 h2 h4 ht

end Funnelling.High