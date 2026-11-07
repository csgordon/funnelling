import Funnelling.High.Typing
import Funnelling.High.WellFormed

namespace Funnelling.High

inductive ECtx where
  | hole
  | callRecv (E : ECtx) (Gs : List GTy) (m : MethName) (es : List Expr)
  | callArg (v : Value) (Gs : List GTy) (m : MethName) (vs : List Value) (E : ECtx) (es : List Expr)
  | superRecv (E : ECtx) (G : GTy) (Gs : List GTy) (m : MethName) (es : List Expr)
  | superArg (v : Value) (G : GTy) (Gs : List GTy) (m : MethName) (vs : List Value) (E : ECtx)
      (es : List Expr)
  | field (E : ECtx) (f : FieldName)
  | newArg (C : ClassName) (Gs : List GTy) (vs : List Value) (E : ECtx) (es : List Expr)
  | localArg (C : ClassName) (Gs : List GTy) (C' : ClassName) (Gs' : List GTy) (vs : List Value)
      (E : ECtx) (es : List Expr) (Ms : List Method)
  | ifCond (E : ECtx) (G : GTy) (x : VarName) (e1 e2 : Expr)

def ECtx.plug : ECtx -> Expr -> Expr
  | .hole, e => e
  | .callRecv E Gs m es, e => .call (E.plug e) Gs m es
  | .callArg v Gs m vs E es, e => .call v Gs m (Value.exprs vs ++ E.plug e :: es)
  | .superRecv E G Gs m es, e => .superCall (E.plug e) G Gs m es
  | .superArg v G Gs m vs E es, e => .superCall v G Gs m (Value.exprs vs ++ E.plug e :: es)
  | .field E f, e => .field (E.plug e) f
  | .newArg C Gs vs E es, e => .new C Gs (Value.exprs vs ++ E.plug e :: es)
  | .localArg C Gs C' Gs' vs E es Ms, e =>
    .newLocal C (Gs.map Funnel.ground) C' Gs' (Value.exprs vs ++ E.plug e :: es) Ms
  | .ifCond E G x e1 e2, e => .ifInst (E.plug e) G x e1 e2

inductive Step (d : Decls) : Expr -> Expr -> Prop
  | simpleFieldFound {D f} {Gs : List GTy} {vs1 vs : List Value} {v : Value} :
      Declared d (.dec D) ->
      vs1.length = D.Ss.length ->
      List.Mem (f, v) ((D.Ss.map Slot.f).zip vs1) ->
      Step d (.field (Value.new D.C Gs (vs1 ++ vs)) f) v
  | simpleFieldSuper {D f} {Gs : List GTy} {vs1 vs : List Value} :
      Declared d (.dec D) ->
      vs1.length = D.Ss.length ->
      Not (List.Mem f (D.Ss.map Slot.f)) ->
      Not (D.C = Object) ->
      Gs.length = D.bounds.length ->
      Step d (.field (Value.new D.C Gs (vs1 ++ vs)) f)
        (.field (.new D.C' (Ty.substList (bind D.bounds (Gs : List Ty)) D.Ts) vs) f)
  | innerFieldSuper {C C' Ms f} {Gs Gs' : List GTy} {vs : List Value} :
      Step d (.field (Value.newLocal C Gs C' Gs' vs Ms) f) (.field (Value.new C' Gs' vs) f)
  | ifThen {C' Ts Ts' x e1 e1' e2} {v : Value} :
      Sub d [] (typeOf v) (.cls C' Ts') ->
      Fresh e1 e1' ->
      VSubstDefined [x] e1' ->
      Step d (.ifInst v (.cls C' Ts) x e1 e2) (e1'.vsubst [(x, v)])
  | ifElse {C' Ts x e1 e2} {v : Value} :
      Not (exists Ts', Sub d [] (typeOf v) (.cls C' Ts')) ->
      Step d (.ifInst v (.cls C' Ts) x e1 e2) e2
  | simpleAddSuper {C m} {v : Value} {Gs Gs' : List GTy} {vs0 vs : List Value} :
      v = Value.new C Gs vs0 ->
      Step d (.call v Gs' m vs) (.superCall v (.cls C Gs) Gs' m vs)
  | simpleFound {D M m Delta' T0 ps e0 e} {v0 : Value} {Gs Gs' : List GTy} {vs : List Value} :
      Declared d (.dec D) ->
      List.Mem M D.Ms ->
      FreshM M (.mk Delta' T0 m ps e0) ->
      (Gs ++ Gs').length = (D.bounds ++ Delta').length ->
      ps.length = vs.length ->
      GSubstDefined (dom D.bounds ++ dom Delta') e0 ->
      VSubstDefined (this :: ps.map VarDecl.x) e0 ->
      e = (e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
        ((this :: ps.map VarDecl.x).zip (v0 :: vs)) ->
      Step d (.superCall v0 (.cls D.C Gs) Gs' m vs) e
  | innerFound {C C' Ms M m Delta' T0 ps e0 e} {v0 : Value} {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} :
      v0 = Value.newLocal C Gs C' Gs'' vs0 Ms ->
      List.Mem M Ms ->
      FreshM M (.mk Delta' T0 m ps e0) ->
      Gs'.length = Delta'.length ->
      ps.length = vs.length ->
      GSubstDefined (dom Delta') e0 ->
      VSubstDefined (this :: ps.map VarDecl.x) e0 ->
      e = (e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs)) ->
      Step d (.call v0 Gs' m vs) e
  | innerSuper {C C' Ms m} {v0 : Value} {Gs0 Gs Gs' : List GTy} {vs0 vs : List Value} :
      v0 = Value.newLocal C Gs0 C' Gs vs0 Ms ->
      Not (List.Mem m (Ms.map Method.name)) ->
      Step d (.call v0 Gs' m vs) (.superCall v0 (.cls C' Gs) Gs' m vs)
  | searchSuper {D m} {v : Value} {Gs Gs' : List GTy} {vs : List Value} :
      Declared d (.dec D) ->
      Not (List.Mem m (D.Ms.map Method.name)) ->
      Not (D.C = Object) ->
      Gs.length = D.bounds.length ->
      Step d (.superCall v (.cls D.C Gs) Gs' m vs)
        (.superCall v (.cls D.C' (Ty.substList (bind D.bounds (Gs : List Ty)) D.Ts)) Gs' m vs)
  | ctx {E : ECtx} {e e'} :
      Step d e e' -> Step d (E.plug e) (E.plug e')

def Reduces (d : Decls) (e e' : Expr) : Prop := Step d e e' /\ WFExpr e'

inductive Steps (d : Decls) : Expr -> Expr -> Prop
  | refl {e} : Steps d e e
  | step {e e' e''} : Reduces d e e' -> Steps d e' e'' -> Steps d e e''

def IsValue (e : Expr) : Prop := exists v : Value, e = v

end Funnelling.High
