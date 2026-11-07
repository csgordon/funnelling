import Funnelling.High.Reduction
import Funnelling.Low.Syntax

namespace Funnelling

mutual
def trTy : High.Ty -> Low.Ty
  | .cls C Ts => .cls C.name (trTys Ts)
  | .var X => .var X.name
def trTys : List High.Ty -> List Low.Ty
  | [] => []
  | T :: Ts => trTy T :: trTys Ts
end

def trFunnel : High.Funnel -> Low.Funnel
  | .ground G => .ground (trTy G.ty)
  | .funnel X => .funnel X.name

def trBounds (Delta : High.Bounds) : Low.Bounds := Delta.map fun b => (b.X.name, trTy b.T)

def trGamma (gamma : High.Gamma) : Low.Ctx := gamma.map fun d => (d.x.name, trTy d.T)

mutual
def trExpr : High.Expr -> Low.Expr
  | .var x => .var x.name
  | .call e Ts m es => .call (trExpr e) (trTys Ts) m.name (trExprs es)
  | .superCall e T Ts m es => .superCall (trExpr e) (trTy T) (trTys Ts) m.name (trExprs es)
  | .field e f => .field (trExpr e) f.name
  | .new C Ts es => .new C.name (trTys Ts) (trExprs es)
  | .newLocal C Fs C' Ts es Ms =>
    .newLocal C.name (Fs.map trFunnel) C'.name (trTys Ts) (trExprs es) (trMethods Ms)
  | .ifInst e0 T x e1 e2 => .ifInst (trExpr e0) (trTy T) x.name (trExpr e1) (trExpr e2)
def trExprs : List High.Expr -> List Low.Expr
  | [] => []
  | e :: es => trExpr e :: trExprs es
def trMethod : High.Method -> Low.Method
  | .mk Delta T0 m ps e =>
    .mk (trBounds Delta) (trTy T0) m.name (ps.map fun d => (trTy d.T, d.x.name)) (trExpr e)
def trMethods : List High.Method -> List Low.Method
  | [] => []
  | M :: Ms => trMethod M :: trMethods Ms
end

def trDec (D : High.Dec) : Low.Dec :=
  { name := D.C.name, bounds := trBounds D.bounds, sup := D.C'.name, supArgs := trTys D.Ts,
    methods := trMethods D.Ms, fields := D.Ss.map fun s => (trTy s.T, s.f.name) }

def trDecls (d : High.Decls) : Low.Decls := d.map trDec

end Funnelling
