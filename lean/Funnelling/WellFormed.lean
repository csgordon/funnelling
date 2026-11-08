import Funnelling.Declarations

namespace Funnelling

mutual
def Expr.locals : Expr -> List K
  | .var _ => []
  | .call e _ _ es => e.locals ++ Expr.localsList es
  | .superCall e _ _ _ es => e.locals ++ Expr.localsList es
  | .field e _ => e.locals
  | .new _ _ es => Expr.localsList es
  | .newLocal C Fs C' Ts es Ms => K.loc C Fs C' Ts es Ms :: (Expr.localsList es ++ Method.localsList Ms)
  | .ifInst e0 _ _ e1 e2 => e0.locals ++ e1.locals ++ e2.locals
def Expr.localsList : List Expr -> List K
  | [] => []
  | e :: es => e.locals ++ Expr.localsList es
def Method.locals : Method -> List K
  | .mk _ _ _ _ e => e.locals
def Method.localsList : List Method -> List K
  | [] => []
  | M :: Ms => M.locals ++ Method.localsList Ms
end

def classes (d : Decls) : List K := d.flatMap fun D => K.dec D :: Method.localsList D.Ms

def Decls.methods (d : Decls) : List Method := (classes d).flatMap K.Ms

def Expr.methods (e : Expr) : List Method := e.locals.flatMap K.Ms

mutual
def Expr.ifVars : Expr -> List VarName
  | .var _ => []
  | .call e _ _ es => e.ifVars ++ Expr.ifVarsList es
  | .superCall e _ _ _ es => e.ifVars ++ Expr.ifVarsList es
  | .field e _ => e.ifVars
  | .new _ _ es => Expr.ifVarsList es
  | .newLocal _ _ _ _ es Ms => Expr.ifVarsList es ++ Method.ifVarsList Ms
  | .ifInst e0 _ x e1 e2 => x :: e0.ifVars ++ e1.ifVars ++ e2.ifVars
def Expr.ifVarsList : List Expr -> List VarName
  | [] => []
  | e :: es => e.ifVars ++ Expr.ifVarsList es
def Method.ifVars : Method -> List VarName
  | .mk _ _ _ _ e => e.ifVars
def Method.ifVarsList : List Method -> List VarName
  | [] => []
  | M :: Ms => M.ifVars ++ Method.ifVarsList Ms
end

mutual
def Expr.noShadow (Xs : List TVarName) (xs : List VarName) : Expr -> Bool
  | .var _ => true
  | .call e _ _ es => e.noShadow Xs xs && Expr.noShadowList Xs xs es
  | .superCall e _ _ _ es => e.noShadow Xs xs && Expr.noShadowList Xs xs es
  | .field e _ => e.noShadow Xs xs
  | .new _ _ es => Expr.noShadowList Xs xs es
  | .newLocal _ _ _ _ es Ms =>
    Expr.noShadowList Xs xs es && Method.noShadowList Xs (xs.filter fun x => x != this) Ms
  | .ifInst e0 _ x e1 e2 =>
    e0.noShadow Xs xs && !(xs.contains x) && e1.noShadow Xs (x :: xs) && e2.noShadow Xs xs
def Expr.noShadowList (Xs : List TVarName) (xs : List VarName) : List Expr -> Bool
  | [] => true
  | e :: es => e.noShadow Xs xs && Expr.noShadowList Xs xs es
def Method.noShadow (Xs : List TVarName) (xs : List VarName) : Method -> Bool
  | .mk Delta _ _ ps e =>
    (dom Delta).all (fun X => !(Xs.contains X)) &&
    (ps.map VarDecl.x).all (fun x => !(xs.contains x)) &&
    e.noShadow (Xs ++ dom Delta) (this :: xs ++ ps.map VarDecl.x)
def Method.noShadowList (Xs : List TVarName) (xs : List VarName) : List Method -> Bool
  | [] => true
  | M :: Ms => M.noShadow Xs xs && Method.noShadowList Xs xs Ms
end

mutual
def Expr.closed (Xs : List TVarName) (xs : List VarName) : Expr -> Bool
  | .var x => xs.contains x
  | .call e Ts _ es => e.closed Xs xs && (Ty.ftvList Ts).all Xs.contains && Expr.closedList Xs xs es
  | .superCall e T Ts _ es =>
    e.closed Xs xs && (Ty.ftvList (T :: Ts)).all Xs.contains && Expr.closedList Xs xs es
  | .field e _ => e.closed Xs xs
  | .new _ Ts es => (Ty.ftvList Ts).all Xs.contains && Expr.closedList Xs xs es
  | .newLocal _ Fs _ Ts es Ms =>
    (domF Fs ++ Ty.ftvList Ts).all Xs.contains && Expr.closedList Xs xs es && Method.closedList Xs xs Ms
  | .ifInst e0 T x e1 e2 =>
    e0.closed Xs xs && T.ftv.all Xs.contains && e1.closed Xs (x :: xs) && e2.closed Xs xs
def Expr.closedList (Xs : List TVarName) (xs : List VarName) : List Expr -> Bool
  | [] => true
  | e :: es => e.closed Xs xs && Expr.closedList Xs xs es
def Method.closed (Xs : List TVarName) (xs : List VarName) : Method -> Bool
  | .mk Delta T0 _ ps e =>
    (Ty.ftvList (T0 :: cod Delta ++ ps.map VarDecl.T)).all (Xs ++ dom Delta).contains &&
    e.closed (Xs ++ dom Delta) (this :: xs ++ ps.map VarDecl.x)
def Method.closedList (Xs : List TVarName) (xs : List VarName) : List Method -> Bool
  | [] => true
  | M :: Ms => M.closed Xs xs && Method.closedList Xs xs Ms
end

def findDec (d : Decls) (C : ClassName) : Option Dec := d.find? fun D => D.C == C

def superChain (d : Decls) : Nat -> ClassName -> List Dec
  | 0, _ => []
  | n + 1, C =>
    match findDec d C with
    | none => []
    | some D => if C == Object then [D] else D :: superChain d n D.C'

abbrev A1 (d : Decls) : Prop := ((classes d).map K.name).Nodup

abbrev A2 (d : Decls) : Prop :=
  forall D, List.Mem D d -> ((superChain d (d.length + 1) D.C).flatMap fun D' => D'.Ss.map Slot.f).Nodup

abbrev A3 (ks : List K) : Prop := forall k, List.Mem k ks -> (k.Ms.map Method.name).Nodup

abbrev A4 (Ms : List Method) : Prop := forall M, List.Mem M Ms -> (M.params.map VarDecl.x).Nodup

abbrev A5 (Deltas : List Bounds) : Prop := forall Delta, List.Mem Delta Deltas -> (dom Delta).Nodup

abbrev A6 (ks : List K) : Prop := forall k, List.Mem k ks -> (domF k.Fs).Nodup

abbrev A7Decls (d : Decls) : Prop :=
  forall D, List.Mem D d -> Method.noShadowList (dom D.bounds) [] D.Ms = true

abbrev A8 (Ms : List Method) (ifVars : List VarName) : Prop :=
  (forall M, List.Mem M Ms -> Not (List.Mem this (M.params.map VarDecl.x))) /\ Not (List.Mem this ifVars)

abbrev A9 (d : Decls) : Prop :=
  (exists D, List.Mem D d /\ D.C = Object /\ D.bounds.isEmpty /\ D.C' = Object /\ D.Ts.isEmpty /\
    D.Ms.isEmpty /\ D.Ss.isEmpty) /\
  forall D, List.Mem D d -> exists D', List.Mem D' (superChain d (d.length + 1) D.C) /\ D'.C = Object

abbrev A10 (d : Decls) : Prop := forall k, List.Mem k (classes d) -> (findDec d k.sup).isSome

abbrev A11 (d : Decls) : Prop := forall k, List.Mem k (classes d) -> forall F, List.Mem F k.Fs -> F.isFunnel
abbrev WFDecls (d : Decls) : Prop :=
  A1 d /\ A2 d /\ A3 (classes d) /\ A4 d.methods /\
  A5 (d.map Dec.bounds ++ d.methods.map Method.bounds) /\ A6 (classes d) /\ A7Decls d /\
  A8 d.methods (d.flatMap fun D => Method.ifVarsList D.Ms) /\ A9 d /\ A10 d /\ A11 d

abbrev WFExpr (e : Expr) : Prop :=
  A3 e.locals /\ A4 e.methods /\ A5 (e.methods.map Method.bounds) /\ A6 e.locals /\
  e.noShadow [] [] = true /\ A8 e.methods e.ifVars /\ e.closed [] [] = true

end Funnelling
