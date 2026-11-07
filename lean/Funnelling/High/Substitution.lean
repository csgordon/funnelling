import Funnelling.High.Syntax

namespace Funnelling.High

abbrev TSubst := List (Prod TVarName Ty)

mutual
def Ty.subst (sigma : TSubst) : Ty -> Ty
  | .var X => (sigma.lookup X).getD (.var X)
  | .cls C Ts => .cls C (Ty.substList sigma Ts)
def Ty.substList (sigma : TSubst) : List Ty -> List Ty
  | [] => []
  | T :: Ts => T.subst sigma :: Ty.substList sigma Ts
end

def substF (Fs : List Funnel) (Ts : List Ty) : TSubst :=
  (Fs.zip Ts).filterMap fun
    | (.funnel X, T) => some (X, T)
    | (.ground _, _) => none

abbrev GSubst := List (Prod TVarName GTy)

def GSubst.ty (sigma : GSubst) : TSubst := sigma.map fun p => (p.1, p.2.ty)

def Funnel.gsubst (sigma : GSubst) : Funnel -> Funnel
  | .ground G => .ground G
  | .funnel X =>
    match sigma.lookup X with
    | some G => .ground G
    | none => .funnel X

def Bounds.subst (sigma : TSubst) (Delta : Bounds) : Bounds :=
  Delta.map fun b => { X := b.X, T := b.T.subst sigma }

def VarDecl.subst (sigma : TSubst) (d : VarDecl) : VarDecl := { T := d.T.subst sigma, x := d.x }

mutual
def Expr.gsubst (sigma : GSubst) : Expr -> Expr
  | .var x => .var x
  | .call e Ts m es => .call (e.gsubst sigma) (Ty.substList sigma.ty Ts) m (Expr.gsubstList sigma es)
  | .superCall e T Ts m es =>
    .superCall (e.gsubst sigma) (T.subst sigma.ty) (Ty.substList sigma.ty Ts) m (Expr.gsubstList sigma es)
  | .field e f => .field (e.gsubst sigma) f
  | .new C Ts es => .new C (Ty.substList sigma.ty Ts) (Expr.gsubstList sigma es)
  | .newLocal C Fs C' Ts es Ms =>
    .newLocal C (Fs.map (Funnel.gsubst sigma)) C' (Ty.substList sigma.ty Ts) (Expr.gsubstList sigma es)
      (Method.gsubstList sigma Ms)
  | .ifInst e0 T x e1 e2 =>
    .ifInst (e0.gsubst sigma) (T.subst sigma.ty) x (e1.gsubst sigma) (e2.gsubst sigma)
def Expr.gsubstList (sigma : GSubst) : List Expr -> List Expr
  | [] => []
  | e :: es => e.gsubst sigma :: Expr.gsubstList sigma es
def Method.gsubst (sigma : GSubst) : Method -> Method
  | .mk Delta T0 m ps e =>
    .mk (Bounds.subst sigma.ty Delta) (T0.subst sigma.ty) m (ps.map (VarDecl.subst sigma.ty)) (e.gsubst sigma)
def Method.gsubstList (sigma : GSubst) : List Method -> List Method
  | [] => []
  | M :: Ms => M.gsubst sigma :: Method.gsubstList sigma Ms
end

abbrev VSubst := List (Prod VarName Value)

mutual
def Expr.vsubst (sigma : VSubst) : Expr -> Expr
  | .var x =>
    match sigma.lookup x with
    | some v => v
    | none => .var x
  | .call e Ts m es => .call (e.vsubst sigma) Ts m (Expr.vsubstList sigma es)
  | .superCall e T Ts m es => .superCall (e.vsubst sigma) T Ts m (Expr.vsubstList sigma es)
  | .field e f => .field (e.vsubst sigma) f
  | .new C Ts es => .new C Ts (Expr.vsubstList sigma es)
  | .newLocal C Fs C' Ts es Ms =>
    .newLocal C Fs C' Ts (Expr.vsubstList sigma es)
      (Method.vsubstList (sigma.filter fun p => p.1 != this) Ms)
  | .ifInst e0 T x e1 e2 => .ifInst (e0.vsubst sigma) T x (e1.vsubst sigma) (e2.vsubst sigma)
def Expr.vsubstList (sigma : VSubst) : List Expr -> List Expr
  | [] => []
  | e :: es => e.vsubst sigma :: Expr.vsubstList sigma es
def Method.vsubst (sigma : VSubst) : Method -> Method
  | .mk Delta T0 m ps e => .mk Delta T0 m ps (e.vsubst sigma)
def Method.vsubstList (sigma : VSubst) : List Method -> List Method
  | [] => []
  | M :: Ms => M.vsubst sigma :: Method.vsubstList sigma Ms
end

abbrev VRen := List (Prod VarName VarName)

abbrev TRen := List (Prod TVarName TVarName)

def VarName.ren (rv : VRen) (x : VarName) : VarName := (rv.lookup x).getD x

def TVarName.ren (rt : TRen) (X : TVarName) : TVarName := (rt.lookup X).getD X

mutual
def Ty.ren (rt : TRen) : Ty -> Ty
  | .var X => .var (X.ren rt)
  | .cls C Ts => .cls C (Ty.renList rt Ts)
def Ty.renList (rt : TRen) : List Ty -> List Ty
  | [] => []
  | T :: Ts => T.ren rt :: Ty.renList rt Ts
end

def Funnel.ren (rt : TRen) : Funnel -> Funnel
  | .ground G => .ground G
  | .funnel X => .funnel (X.ren rt)

mutual
inductive RenE : VRen -> TRen -> Expr -> Expr -> Prop
  | var {rv rt x} : RenE rv rt (.var x) (.var (x.ren rv))
  | call {rv rt e e' Ts m es es'} :
      RenE rv rt e e' -> RenEs rv rt es es' ->
      RenE rv rt (.call e Ts m es) (.call e' (Ty.renList rt Ts) m es')
  | superCall {rv rt e e' T Ts m es es'} :
      RenE rv rt e e' -> RenEs rv rt es es' ->
      RenE rv rt (.superCall e T Ts m es) (.superCall e' (T.ren rt) (Ty.renList rt Ts) m es')
  | field {rv rt e e' f} :
      RenE rv rt e e' -> RenE rv rt (.field e f) (.field e' f)
  | new {rv rt C Ts es es'} :
      RenEs rv rt es es' -> RenE rv rt (.new C Ts es) (.new C (Ty.renList rt Ts) es')
  | newLocal {rv rt C Fs C' Ts es es' Ms Ms'} :
      RenEs rv rt es es' -> RenMs rv rt Ms Ms' ->
      RenE rv rt (.newLocal C Fs C' Ts es Ms)
        (.newLocal C (Fs.map (Funnel.ren rt)) C' (Ty.renList rt Ts) es' Ms')
  | ifInst {rv rt e0 e0' T x y e1 e1' e2 e2'} :
      RenE rv rt e0 e0' -> RenE ((x, y) :: rv) rt e1 e1' -> RenE rv rt e2 e2' ->
      RenE rv rt (.ifInst e0 T x e1 e2) (.ifInst e0' (T.ren rt) y e1' e2')
inductive RenEs : VRen -> TRen -> List Expr -> List Expr -> Prop
  | nil {rv rt} : RenEs rv rt [] []
  | cons {rv rt e e' es es'} : RenE rv rt e e' -> RenEs rv rt es es' -> RenEs rv rt (e :: es) (e' :: es')
inductive RenM : VRen -> TRen -> Method -> Method -> Prop
  | mk {rv rt Delta T0 m ps e e' Xs' xs'} :
      Xs'.length = Delta.length -> xs'.length = ps.length ->
      RenE ((ps.map VarDecl.x).zip xs' ++ rv) ((dom Delta).zip Xs' ++ rt) e e' ->
      RenM rv rt (.mk Delta T0 m ps e)
        (.mk ((Delta.zip Xs').map fun p =>
                { X := p.2, T := p.1.T.ren ((dom Delta).zip Xs' ++ rt) })
          (T0.ren ((dom Delta).zip Xs' ++ rt)) m
          ((ps.zip xs').map fun p => { T := p.1.T.ren ((dom Delta).zip Xs' ++ rt), x := p.2 }) e')
inductive RenMs : VRen -> TRen -> List Method -> List Method -> Prop
  | nil {rv rt} : RenMs rv rt [] []
  | cons {rv rt M M' Ms Ms'} : RenM rv rt M M' -> RenMs rv rt Ms Ms' -> RenMs rv rt (M :: Ms) (M' :: Ms')
end

mutual
def Expr.vbinders : Expr -> List VarName
  | .var _ => []
  | .call e _ _ es => e.vbinders ++ Expr.vbindersList es
  | .superCall e _ _ _ es => e.vbinders ++ Expr.vbindersList es
  | .field e _ => e.vbinders
  | .new _ _ es => Expr.vbindersList es
  | .newLocal _ _ _ _ es Ms => Expr.vbindersList es ++ Method.vbindersList Ms
  | .ifInst e0 _ x e1 e2 => x :: e0.vbinders ++ e1.vbinders ++ e2.vbinders
def Expr.vbindersList : List Expr -> List VarName
  | [] => []
  | e :: es => e.vbinders ++ Expr.vbindersList es
def Method.vbinders : Method -> List VarName
  | .mk _ _ _ ps e => ps.map VarDecl.x ++ e.vbinders
def Method.vbindersList : List Method -> List VarName
  | [] => []
  | M :: Ms => M.vbinders ++ Method.vbindersList Ms
end

mutual
def Expr.tbinders : Expr -> List TVarName
  | .var _ => []
  | .call e _ _ es => e.tbinders ++ Expr.tbindersList es
  | .superCall e _ _ _ es => e.tbinders ++ Expr.tbindersList es
  | .field e _ => e.tbinders
  | .new _ _ es => Expr.tbindersList es
  | .newLocal _ _ _ _ es Ms => Expr.tbindersList es ++ Method.tbindersList Ms
  | .ifInst e0 _ _ e1 e2 => e0.tbinders ++ e1.tbinders ++ e2.tbinders
def Expr.tbindersList : List Expr -> List TVarName
  | [] => []
  | e :: es => e.tbinders ++ Expr.tbindersList es
def Method.tbinders : Method -> List TVarName
  | .mk Delta _ _ _ e => dom Delta ++ e.tbinders
def Method.tbindersList : List Method -> List TVarName
  | [] => []
  | M :: Ms => M.tbinders ++ Method.tbindersList Ms
end

structure Names where
  xs : List VarName
  Xs : List TVarName

abbrev FreshNames (avoid : Names) (xs : List VarName) (Xs : List TVarName) : Prop :=
  xs.Nodup /\ Xs.Nodup /\ xs.all (fun x => !(avoid.xs.contains x)) = true /\
    Xs.all (fun X => !(avoid.Xs.contains X)) = true

def Fresh (avoid : Names) (e e' : Expr) : Prop :=
  RenE [] [] e e' /\ FreshNames avoid e'.vbinders e'.tbinders

def FreshM (avoid : Names) (M M' : Method) : Prop :=
  RenM [] [] M M' /\ FreshNames avoid M'.vbinders M'.tbinders

end Funnelling.High
