import Funnelling.High.Substitution

namespace Funnelling.High

inductive ExprCtx where
  | hole
  | callRecv (ctx : ExprCtx) (Ts : List Ty) (m : MethName) (es : List Expr)
  | callArg (e : Expr) (Ts : List Ty) (m : MethName) (es : List Expr) (ctx : ExprCtx) (es' : List Expr)
  | superRecv (ctx : ExprCtx) (T : Ty) (Ts : List Ty) (m : MethName) (es : List Expr)
  | superArg (e : Expr) (T : Ty) (Ts : List Ty) (m : MethName) (es : List Expr) (ctx : ExprCtx)
      (es' : List Expr)
  | field (ctx : ExprCtx) (f : FieldName)
  | newArg (C : ClassName) (Ts : List Ty) (es : List Expr) (ctx : ExprCtx) (es' : List Expr)
  | localArg (C : ClassName) (Fs : List Funnel) (C' : ClassName) (Ts : List Ty) (es : List Expr)
      (ctx : ExprCtx) (es' : List Expr) (Ms : List Method)
  | ifCond (ctx : ExprCtx) (T : Ty) (x : VarName) (e1 e2 : Expr)
  | ifThen (e0 : Expr) (T : Ty) (x : VarName) (ctx : ExprCtx) (e2 : Expr)
  | ifElse (e0 : Expr) (T : Ty) (x : VarName) (e1 : Expr) (ctx : ExprCtx)

def ExprCtx.plug : ExprCtx -> Expr -> Expr
  | .hole, e => e
  | .callRecv ctx Ts m es, e => .call (ctx.plug e) Ts m es
  | .callArg e0 Ts m es ctx es', e => .call e0 Ts m (es ++ ctx.plug e :: es')
  | .superRecv ctx T Ts m es, e => .superCall (ctx.plug e) T Ts m es
  | .superArg e0 T Ts m es ctx es', e => .superCall e0 T Ts m (es ++ ctx.plug e :: es')
  | .field ctx f, e => .field (ctx.plug e) f
  | .newArg C Ts es ctx es', e => .new C Ts (es ++ ctx.plug e :: es')
  | .localArg C Fs C' Ts es ctx es' Ms, e => .newLocal C Fs C' Ts (es ++ ctx.plug e :: es') Ms
  | .ifCond ctx T x e1 e2, e => .ifInst (ctx.plug e) T x e1 e2
  | .ifThen e0 T x ctx e2, e => .ifInst e0 T x (ctx.plug e) e2
  | .ifElse e0 T x e1 ctx, e => .ifInst e0 T x e1 (ctx.plug e)

def OccursIn (e' e : Expr) : Prop := exists ctx : ExprCtx, e = ctx.plug e'

def MemK (M : Method) (k : K) : Prop := List.Mem M k.Ms

inductive Declared (d : Decls) : K -> Prop
  | dec {D} : List.Mem D d -> Declared d (.dec D)
  | loc {k Delta T0 m ps e C0 Fs C' Ts es Ms} :
      Declared d k -> MemK (.mk Delta T0 m ps e) k ->
      OccursIn (.newLocal C0 Fs C' Ts es Ms) e ->
      Declared d (.loc C0 Fs C' Ts es Ms)

def MethodIn (d : Decls) (M : Method) (C : ClassName) : Prop :=
  exists k, Declared d k /\ k.name = C /\ MemK M k

inductive Generic (d : Decls) : ClassName -> Ty -> Prop
  | dec {D} : Declared d (.dec D) -> Generic d D.C (.cls D.C (vars (dom D.bounds)))
  | loc {C Fs C' Ts es Ms} :
      Declared d (.loc C Fs C' Ts es Ms) -> Generic d C (.cls C (vars (domF Fs)))

inductive Pairing (Delta : Bounds) : List Funnel -> List Ty -> Bounds -> List Ty -> Prop
  | nil : Pairing Delta [] [] [] []
  | funnel {X T T0 Fs Ts Delta' Ts'} :
      List.Mem { X := X, T := T } Delta -> Pairing Delta Fs Ts Delta' Ts' ->
      Pairing Delta (.funnel X :: Fs) (T0 :: Ts) ({ X := X, T := T } :: Delta') (T0 :: Ts')
  | ground {G Fs Ts Delta' Ts'} :
      Pairing Delta Fs Ts Delta' Ts' -> Pairing Delta (.ground G :: Fs) (G.ty :: Ts) Delta' Ts'

inductive Scope (d : Decls) : Ty -> Bounds -> List Ty -> Prop
  | dec {D Ts} : Declared d (.dec D) -> Scope d (.cls D.C Ts) D.bounds Ts
  | loc {C Delta' T0 m ps e C0 Fs C' Ts' es Ms T Delta Ts'' Ts Delta0 Ts0} :
      MethodIn d (.mk Delta' T0 m ps e) C ->
      OccursIn (.newLocal C0 Fs C' Ts' es Ms) e ->
      Generic d C T -> Scope d T Delta Ts'' ->
      Pairing (Delta ++ Delta') Fs Ts Delta0 Ts0 ->
      Scope d (.cls C0 Ts) Delta0 Ts0

def typeOf : Value -> Ty
  | .new C Gs _ => .cls C (GTy.tys Gs)
  | .newLocal C Gs _ _ _ _ => .cls C (GTy.tys Gs)

end Funnelling.High
