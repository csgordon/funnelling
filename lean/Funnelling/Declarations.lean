import Funnelling.Substitution

namespace Funnelling

inductive ExprCtx where
  | hole
  | callRecv (ctx : ExprCtx) (Ts : List Ty) (m : MethName) (es : List Expr)
  | callArg (e : Expr) (Ts : List Ty) (m : MethName) (es : List Expr) (ctx : ExprCtx) (es' : List Expr)
  | superRecv (ctx : ExprCtx) (T : Ty) (Ts : List Ty) (m : MethName) (es : List Expr)
  | superArg (e : Expr) (T : Ty) (Ts : List Ty) (m : MethName) (es : List Expr) (ctx : ExprCtx)
      (es' : List Expr)
  | field (ctx : ExprCtx) (f : FieldName)
  | newArg (C : ClassName) (Ts : List Ty) (es : List Expr) (ctx : ExprCtx) (es' : List Expr)
  | newLocalArg (C : ClassName) (Fs : List Funnel) (C' : ClassName) (Ts : List Ty) (es : List Expr)
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
  | .newLocalArg C Fs C' Ts es ctx es' Ms, e => .newLocal C Fs C' Ts (es ++ ctx.plug e :: es') Ms
  | .ifCond ctx T x e1 e2, e => .ifInst (ctx.plug e) T x e1 e2
  | .ifThen e0 T x ctx e2, e => .ifInst e0 T x (ctx.plug e) e2
  | .ifElse e0 T x e1 ctx, e => .ifInst e0 T x e1 (ctx.plug e)

def OccursIn (e' e : Expr) : Prop := exists ctx : ExprCtx, e = ctx.plug e'

inductive Declared (d : Decls) : ClassDecl -> Prop
  | dec {D} : List.Mem D d -> Declared d (.dec D)
  | newLocal {K Delta T0 m ps e C0 Fs C' Ts es Ms} :
      Declared d K -> List.Mem (.mk Delta T0 m ps e) K.Ms ->
      OccursIn (.newLocal C0 Fs C' Ts es Ms) e ->
      Declared d (.newLocal C0 Fs C' Ts es Ms)

def MethodIn (d : Decls) (M : Method) (C : ClassName) : Prop :=
  exists K, Declared d K /\ K.name = C /\ List.Mem M K.Ms

inductive Generic (d : Decls) : ClassName -> Ty -> Prop
  | dec {D} : Declared d (.dec D) -> Generic d D.C (.cls D.C (vars (dom D.Delta)))
  | newLocal {C Fs C' Ts es Ms} :
      Declared d (.newLocal C Fs C' Ts es Ms) -> Generic d C (.cls C (vars (domF Fs)))

inductive RestrictB (Delta : Bounds) : List Funnel -> Bounds -> Prop
  | nil : RestrictB Delta [] []
  | funnel {X T Fs Delta'} :
      List.Mem { X := X, T := T } Delta -> RestrictB Delta Fs Delta' ->
      RestrictB Delta (.funnel X :: Fs) ({ X := X, T := T } :: Delta')
  | ground {G Fs Delta'} : RestrictB Delta Fs Delta' -> RestrictB Delta (.ground G :: Fs) Delta'

inductive Scope (d : Decls) : ClassName -> Bounds -> Prop
  | dec {D} : Declared d (.dec D) -> Scope d D.C D.Delta
  | newLocal {C Delta' T0 m ps e C0 Fs C' Ts' es Ms Delta Delta0} :
      MethodIn d (.mk Delta' T0 m ps e) C ->
      OccursIn (.newLocal C0 Fs C' Ts' es Ms) e ->
      Scope d C Delta ->
      RestrictB (Delta ++ Delta') Fs Delta0 ->
      Scope d C0 Delta0

def typeOf : Value -> Ty
  | .new C Gs _ => .cls C Gs
  | .newLocal C Gs _ _ _ _ => .cls C Gs

end Funnelling
