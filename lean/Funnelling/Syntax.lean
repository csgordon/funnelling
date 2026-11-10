namespace Funnelling

structure ClassName where
  name : String
  deriving DecidableEq, Repr

structure MethName where
  name : String
  deriving DecidableEq, Repr

structure FieldName where
  name : String
  deriving DecidableEq, Repr

structure VarName where
  name : String
  deriving DecidableEq, Repr

structure TVarName where
  name : String
  deriving DecidableEq, Repr

def Object : ClassName := { name := "Object" }

def this : VarName := { name := "this" }

inductive Ty where
  | cls (C : ClassName) (Ts : List Ty)
  | var (X : TVarName)
  deriving Repr

inductive GTy where
  | cls (C : ClassName) (Gs : List GTy)
  deriving Repr

inductive Funnel where
  | ground (G : GTy)
  | funnel (X : TVarName)
  deriving Repr

structure Bound where
  X : TVarName
  T : Ty
  deriving Repr

structure VarDecl where
  T : Ty
  x : VarName
  deriving Repr

structure Slot where
  T : Ty
  f : FieldName
  deriving Repr

abbrev Bounds := List Bound

abbrev TypeEnv := List VarDecl

mutual
inductive Expr where
  | var (x : VarName)
  | call (e : Expr) (Ts : List Ty) (m : MethName) (es : List Expr)
  | superCall (e : Expr) (T : Ty) (Ts : List Ty) (m : MethName) (es : List Expr)
  | field (e : Expr) (f : FieldName)
  | new (C : ClassName) (Ts : List Ty) (es : List Expr)
  | newLocal (C : ClassName) (Fs : List Funnel) (C' : ClassName) (Ts : List Ty) (es : List Expr)
      (Ms : List Method)
  | ifInst (e0 : Expr) (T : Ty) (x : VarName) (e1 e2 : Expr)
  deriving Repr
inductive Method where
  | mk (Delta : Bounds) (T0 : Ty) (m : MethName) (ps : List VarDecl) (e : Expr)
  deriving Repr
end

inductive Value where
  | new (C : ClassName) (Gs : List GTy) (vs : List Value)
  | newLocal (C : ClassName) (Gs : List GTy) (C' : ClassName) (Gs' : List GTy) (vs : List Value)
      (Ms : List Method)
  deriving Repr

structure Dec where
  C : ClassName
  Delta : Bounds
  C' : ClassName
  Ts : List Ty
  Ms : List Method
  Ss : List Slot
  deriving Repr

inductive ClassDecl where
  | dec (D : Dec)
  | newLocal (C : ClassName) (Fs : List Funnel) (C' : ClassName) (Ts : List Ty) (es : List Expr)
      (Ms : List Method)
  deriving Repr

abbrev Decls := List Dec

mutual
def GTy.ty : GTy -> Ty
  | .cls C Gs => .cls C (GTy.tys Gs)
def GTy.tys : List GTy -> List Ty
  | [] => []
  | G :: Gs => G.ty :: GTy.tys Gs
end

instance : Coe GTy Ty where
  coe := GTy.ty

mutual
def Value.expr : Value -> Expr
  | .new C Gs vs => .new C (GTy.tys Gs) (Value.exprs vs)
  | .newLocal C Gs C' Gs' vs Ms => .newLocal C (Gs.map Funnel.ground) C' (GTy.tys Gs') (Value.exprs vs) Ms
def Value.exprs : List Value -> List Expr
  | [] => []
  | v :: vs => v.expr :: Value.exprs vs
end

instance : Coe Value Expr where
  coe := Value.expr

instance : Coe (List GTy) (List Ty) where
  coe := GTy.tys

instance : Coe (List Value) (List Expr) where
  coe := Value.exprs

def Method.name : Method -> MethName
  | .mk _ _ m _ _ => m

def Method.Delta : Method -> Bounds
  | .mk Delta _ _ _ _ => Delta

def Method.params : Method -> List VarDecl
  | .mk _ _ _ ps _ => ps

def Method.body : Method -> Expr
  | .mk _ _ _ _ e => e

def ClassDecl.name : ClassDecl -> ClassName
  | .dec D => D.C
  | .newLocal C _ _ _ _ _ => C

def ClassDecl.Ms : ClassDecl -> List Method
  | .dec D => D.Ms
  | .newLocal _ _ _ _ _ Ms => Ms

def ClassDecl.sup : ClassDecl -> ClassName
  | .dec D => D.C'
  | .newLocal _ _ C' _ _ _ => C'

def ClassDecl.Fs : ClassDecl -> List Funnel
  | .dec _ => []
  | .newLocal _ Fs _ _ _ _ => Fs

def dom (Delta : Bounds) : List TVarName := Delta.map Bound.X

def cod (Delta : Bounds) : List Ty := Delta.map Bound.T

def domF (Fs : List Funnel) : List TVarName :=
  Fs.filterMap fun
    | .funnel X => some X
    | .ground _ => none

def Funnel.abs : Funnel -> Ty
  | .ground G => G
  | .funnel X => .var X

def abs (Fs : List Funnel) : List Ty := Fs.map Funnel.abs

def vars (Xs : List TVarName) : List Ty := Xs.map Ty.var

mutual
def Ty.ftv : Ty -> List TVarName
  | .var X => [X]
  | .cls _ Ts => Ty.ftvList Ts
def Ty.ftvList : List Ty -> List TVarName
  | [] => []
  | T :: Ts => T.ftv ++ Ty.ftvList Ts
end

def TypeEnv.lookup (Gamma : TypeEnv) (x : VarName) : Option Ty :=
  (Gamma.find? fun d => d.x == x).map VarDecl.T

instance memDecidable {A : Type} [DecidableEq A] (a : A) (l : List A) : Decidable (List.Mem a l) :=
  inferInstanceAs (Decidable (Membership.mem l a))

instance forallMemDecidable {A : Type} (l : List A) (p : A -> Prop) [DecidablePred p] :
    Decidable (forall x, List.Mem x l -> p x) :=
  inferInstanceAs (Decidable (forall x, Membership.mem l x -> p x))

instance existsMemDecidable {A : Type} (l : List A) (p : A -> Prop) [DecidablePred p] :
    Decidable (exists x, List.Mem x l /\ p x) :=
  inferInstanceAs (Decidable (exists x, Membership.mem l x /\ p x))

def Funnel.isFunnel : Funnel -> Bool
  | .funnel _ => true
  | .ground _ => false

end Funnelling
