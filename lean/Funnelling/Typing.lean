import Funnelling.Declarations

namespace Funnelling

inductive Seq2 {A B : Type} (R : A -> B -> Prop) : List A -> List B -> Prop
  | nil : Seq2 R [] []
  | cons {a b as bs} : R a b -> Seq2 R as bs -> Seq2 R (a :: as) (b :: bs)

inductive Sub (d : Decls) (Delta : Bounds) : Ty -> Ty -> Prop
  | subRefl {T} : Sub d Delta T T
  | subInherit {D Ts0 T'} :
      Declared d (.dec D) ->
      Ts0.length = D.bounds.length ->
      Sub d Delta ((Ty.cls D.C' D.Ts).subst (bind D.bounds Ts0)) T' ->
      Sub d Delta (.cls D.C Ts0) T'
  | subInheritLocal {C Fs C' Ts' es Ms Ts T'} :
      Declared d (.loc C Fs C' Ts' es Ms) ->
      Ts.length = Fs.length ->
      Sub d Delta ((Ty.cls C' Ts').subst (bindF Fs Ts)) T' ->
      Sub d Delta (.cls C Ts) T'
  | subVar {X T T'} :
      List.Mem { X := X, T := T } Delta -> Sub d Delta T T' -> Sub d Delta (.var X) T'

abbrev SubSeq (d : Decls) (Delta : Bounds) : List Ty -> List Ty -> Prop := Seq2 (Sub d Delta)

inductive Kind (d : Decls) (Delta : Bounds) : Ty -> Prop
  | wfVar {X T} : List.Mem { X := X, T := T } Delta -> Kind d Delta (.var X)
  | wfClass {C Ts Delta0 Ts0} :
      Scope d (.cls C Ts) Delta0 Ts0 ->
      (forall T, List.Mem T Ts -> Kind d Delta T) ->
      Ts0.length = Delta0.length ->
      SubSeq d Delta Ts0 (Ty.substList (bind Delta0 Ts0) (cod Delta0)) ->
      Kind d Delta (.cls C Ts)

abbrev KindSeq (d : Decls) (Delta : Bounds) (Ts : List Ty) : Prop := forall T, List.Mem T Ts -> Kind d Delta T

inductive Cast (d : Decls) (Delta : Bounds) : Ty -> Ty -> Prop
  | castUp {T T'} : Sub d Delta T T' -> Cast d Delta T T'
  | castVar {X T T'} :
      List.Mem { X := X, T := T } Delta -> Cast d Delta T T' -> Cast d Delta (.var X) T'
  | castDown {C Ts C' Ts0 Xs Ts'} :
      Sub d Delta (.cls C Ts) (.cls C' Ts0) ->
      Generic d C (.cls C (vars Xs)) ->
      Sub d [] (.cls C (vars Xs)) (.cls C' Ts') ->
      (forall X, List.Mem X Xs -> List.Mem X (Ty.ftvList Ts')) ->
      Cast d Delta (.cls C' Ts0) (.cls C Ts)

inductive OverrideOkM (d : Decls) : Ty -> Method -> Prop
  | absent {D Ts Delta' T0' m ps' e'} :
      Declared d (.dec D) ->
      Not (List.Mem m (D.Ms.map Method.name)) ->
      OverrideOkM d (.cls D.C Ts) (.mk Delta' T0' m ps' e')
  | dec {D Ts Delta' T0' m ps' e' Delta'' T0 ps e} :
      Declared d (.dec D) ->
      List.Mem (Method.mk Delta'' T0 m ps e) D.Ms ->
      Ts.length = D.bounds.length -> Delta'.length = Delta''.length ->
      Ty.substList (bind (D.bounds ++ Delta'') (Ts ++ vars (dom Delta'))) (cod Delta'')
        = cod Delta' ->
      Ty.substList (bind (D.bounds ++ Delta'') (Ts ++ vars (dom Delta')))
        (T0 :: ps.map VarDecl.T) = T0' :: ps'.map VarDecl.T ->
      OverrideOkM d (.cls D.C Ts) (.mk Delta' T0' m ps' e')
  | loc {C Fs C0 Ts0 es Ms Ts Delta' T0' m ps' e' Delta'' T0 ps e} :
      Declared d (.loc C Fs C0 Ts0 es Ms) ->
      List.Mem (Method.mk Delta'' T0 m ps e) Ms ->
      Ts.length = Fs.length -> Delta'.length = Delta''.length ->
      Ty.substList (bindF Fs Ts ++ bind Delta'' (vars (dom Delta'))) (cod Delta'')
        = cod Delta' ->
      Ty.substList (bindF Fs Ts ++ bind Delta'' (vars (dom Delta')))
        (T0 :: ps.map VarDecl.T) = T0' :: ps'.map VarDecl.T ->
      OverrideOkM d (.cls C Ts) (.mk Delta' T0' m ps' e')

def OverrideOk (d : Decls) (Delta : Bounds) (T : Ty) (Ms : List Method) : Prop :=
  forall M C Ts, List.Mem M Ms -> Sub d Delta T (.cls C Ts) -> OverrideOkM d (.cls C Ts) M

def Consistent (d : Decls) : K -> Prop
  | .loc C Fs C0 Ts _ Ms =>
    exists Fs' Ts' es' Ms',
      Declared d (.loc C Fs' C0 Ts' es' Ms') /\
      Fs.length = Fs'.length /\
      Ts = Ty.substList (bindF Fs' (abs Fs)) Ts' /\
      (forall m, List.Mem m (Ms'.map Method.name) <-> List.Mem m (Ms.map Method.name)) /\
      forall M, List.Mem M Ms -> OverrideOkM d (.cls C (abs Fs)) M
  | .dec _ => False

def restrict (gamma : Gamma) (Xs : List TVarName) : Gamma :=
  gamma.filter fun d => (Ty.ftv d.T).all fun X => Xs.contains X

def withoutThis (gamma : Gamma) : Gamma := gamma.filter fun d => d.x != this

mutual
inductive Typing (d : Decls) : Bounds -> Gamma -> Expr -> Ty -> Prop
  | subs {Delta gamma e T1 T2} :
      Typing d Delta gamma e T1 -> Kind d Delta T2 -> Sub d Delta T1 T2 ->
      Typing d Delta gamma e T2
  | var {Delta gamma x T} :
      gamma.lookup x = some T -> Typing d Delta gamma (.var x) T
  | newObject {Delta gamma} :
      Typing d Delta gamma (.new Object [] []) (.cls Object [])
  | declField {Delta gamma e D Ts' T f} :
      Typing d Delta gamma e (.cls D.C Ts') ->
      Declared d (.dec D) ->
      List.Mem { T := T, f := f } D.Ss ->
      Ts'.length = D.bounds.length ->
      Typing d Delta gamma (.field e f) (T.subst (bind D.bounds Ts'))
  | call {Delta gamma e0 C0 Ts0 Delta0 Ts2 Delta1 T0 m ps body Ts1 es T0' Ts'} :
      Typing d Delta gamma e0 (.cls C0 Ts0) ->
      Scope d (.cls C0 Ts0) Delta0 Ts2 ->
      MethodIn d (.mk Delta1 T0 m ps body) C0 ->
      Ts2.length = Delta0.length -> Ts1.length = Delta1.length ->
      T0' :: Ts' = Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ Ts1)) (T0 :: ps.map VarDecl.T) ->
      KindSeq d Delta Ts1 ->
      SubSeq d Delta Ts1 (Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ Ts1)) (cod Delta1)) ->
      TypingSeq d Delta gamma es Ts' ->
      Typing d Delta gamma (.call e0 Ts1 m es) T0'
  | callLbRuntime {Delta gamma e0 D Ts D0 Ts0 Delta1 T0 m ps body Ts1 es T0' Ts'} :
      Sub d Delta (.cls D.C Ts) (.cls D0.C Ts0) ->
      Declared d (.dec D0) ->
      MethodIn d (.mk Delta1 T0 m ps body) D0.C ->
      Ts0.length = D0.bounds.length -> Ts1.length = Delta1.length ->
      T0' :: Ts' = Ty.substList (bind (D0.bounds ++ Delta1) (Ts0 ++ Ts1)) (T0 :: ps.map VarDecl.T) ->
      Declared d (.dec D) ->
      Kind d Delta (.cls D.C Ts) ->
      KindSeq d Delta Ts1 ->
      SubSeq d Delta Ts1 (Ty.substList (bind (D0.bounds ++ Delta1) (Ts0 ++ Ts1)) (cod Delta1)) ->
      TypingSeq d Delta gamma (e0 :: es) (.cls D.C Ts :: Ts') ->
      Typing d Delta gamma (.superCall e0 (.cls D.C Ts) Ts1 m es) T0'
  | newTop {Delta gamma D Ts' es1 es2 T''} :
      Declared d (.dec D) ->
      Kind d Delta (.cls D.C Ts') ->
      Ts'.length = D.bounds.length ->
      TypingSeq d Delta gamma es1 (Ty.substList (bind D.bounds Ts') (D.Ss.map Slot.T)) ->
      Typing d Delta gamma (.new D.C' (Ty.substList (bind D.bounds Ts') D.Ts) es2) T'' ->
      Typing d Delta gamma (.new D.C Ts' (es1 ++ es2)) (.cls D.C Ts')
  | newLocal {Delta gamma C Fs C0 Ts es Ms Delta' Ts'' T''} :
      Consistent d (.loc C Fs C0 Ts es Ms) ->
      Pairing Delta Fs (abs Fs) Delta' Ts'' ->
      (forall X, List.Mem X (Ty.ftvList (cod Delta')) -> List.Mem X (dom Delta')) ->
      Kind d Delta' (.cls C (abs Fs)) ->
      Kind d Delta' (.cls C0 Ts) ->
      Typing d Delta gamma (.new C0 Ts es) T'' ->
      (forall M, List.Mem M Ms ->
        MethodOk d Delta'
          (withoutThis (restrict gamma (Ty.ftvList (abs Fs))) ++ [{ T := .cls C (abs Fs), x := this }]) M) ->
      OverrideOk d Delta' (.cls C0 Ts) Ms ->
      Typing d Delta gamma (.newLocal C Fs C0 Ts es Ms) (.cls C (abs Fs))
  | ifInstanceof {Delta gamma e0 T0 T x e1 e2 T'} :
      Typing d Delta gamma e0 T0 ->
      Kind d Delta T ->
      Cast d Delta T0 T ->
      Typing d Delta (gamma ++ [{ T := T, x := x }]) e1 T' ->
      Typing d Delta gamma e2 T' ->
      Typing d Delta gamma (.ifInst e0 T x e1 e2) T'
inductive TypingSeq (d : Decls) : Bounds -> Gamma -> List Expr -> List Ty -> Prop
  | nil {Delta gamma} : TypingSeq d Delta gamma [] []
  | cons {Delta gamma e es T Ts} :
      Typing d Delta gamma e T -> TypingSeq d Delta gamma es Ts ->
      TypingSeq d Delta gamma (e :: es) (T :: Ts)
inductive MethodOk (d : Decls) : Bounds -> Gamma -> Method -> Prop
  | methodOk {Delta gamma Delta' T0 m ps e} :
      KindSeq d (Delta ++ Delta') (cod Delta') ->
      KindSeq d (Delta ++ Delta') (T0 :: ps.map VarDecl.T) ->
      Typing d (Delta ++ Delta') (gamma ++ ps) e T0 ->
      MethodOk d Delta gamma (.mk Delta' T0 m ps e)
end

def ClassOk (d : Decls) (D : Dec) : Prop :=
  KindSeq d D.bounds (cod D.bounds) /\
  KindSeq d D.bounds (Ty.cls D.C' D.Ts :: D.Ss.map Slot.T) /\
  (forall M, List.Mem M D.Ms ->
    MethodOk d D.bounds [{ T := .cls D.C (vars (dom D.bounds)), x := this }] M) /\
  OverrideOk d D.bounds (.cls D.C' D.Ts) D.Ms

def DeclsOk (d : Decls) : Prop := forall D, List.Mem D d -> ClassOk d D

def ProgOk (d : Decls) (e : Expr) : Prop :=
  DeclsOk d /\ exists T, Typing d [] [] e T

end Funnelling
