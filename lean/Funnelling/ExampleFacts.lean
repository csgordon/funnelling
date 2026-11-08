import Funnelling.Soundness

namespace Funnelling.ExampleFacts

open Funnelling

mutual
def toG : Ty -> GTy
  | .cls C Ts => .cls C (toGs Ts)
  | .var _ => .cls Object []
def toGs : List Ty -> List GTy
  | [] => []
  | T :: Ts => toG T :: toGs Ts
end

def fGround : Funnel -> GTy
  | .ground G => G
  | .funnel _ => .cls Object []

mutual
def toV : Expr -> Value
  | .new C Ts es => .new C (toGs Ts) (toVs es)
  | .newLocal C Fs C' Ts es Ms => .newLocal C (Fs.map fGround) C' (toGs Ts) (toVs es) Ms
  | _ => .new Object [] []
def toVs : List Expr -> List Value
  | [] => []
  | e :: es => toV e :: toVs es
end

theorem tys_length {Gs : List GTy} {Ts : List Ty} (h : GTy.tys Gs = Ts) : Gs.length = Ts.length := by
  rw [<- h, GTy.tys_eq_map, List.length_map]

theorem exprs_length {vs : List Value} {es : List Expr} (h : Value.exprs vs = es) : vs.length = es.length := by
  rw [<- h, Value.exprs_eq_map, List.length_map]

theorem idNil {A : Type} : forall p, List.Mem p ([] : List (Prod A A)) -> p.1 = p.2 := by
  intro p hp; cases hp

theorem freshM (M : Method) : FreshM M M := And.intro (RenM.refl idNil idNil M) (RenM.refl idNil idNil M)

theorem sAdd {d : Decls} {C : ClassName} {Ts0 : List Ty} {es0 : List Expr} {Ts : List Ty} {m : MethName}
    {es : List Expr} (h0 : GTy.tys (toGs Ts0) = Ts0) (h1 : Value.exprs (toVs es0) = es0)
    (h2 : GTy.tys (toGs Ts) = Ts) (h3 : Value.exprs (toVs es) = es) :
    Step d (.call (.new C Ts0 es0) Ts m es) (.superCall (.new C Ts0 es0) (.cls C Ts0) Ts m es) := by
  have h := Step.simpleAddSuper (d := d) (C := C) (m := m) (v := .new C (toGs Ts0) (toVs es0)) (Gs := toGs Ts0)
    (Gs' := toGs Ts) (vs0 := toVs es0) (vs := toVs es) rfl
  simp only [Value.expr] at h
  rw [h0, h1, h2, h3] at h
  exact h

theorem sFound {d : Decls} {D : Dec} {Delta' : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl} {e0 : Expr}
    {r : Expr} {Ts Ts' : List Ty} {es : List Expr}
    (hD : List.Mem D d) (hM : List.Mem (Method.mk Delta' T0 m ps e0) D.Ms)
    (h1 : (toV r).expr = r) (h2 : GTy.tys (toGs Ts) = Ts) (h3 : GTy.tys (toGs Ts') = Ts')
    (h4 : Value.exprs (toVs es) = es)
    (l1 : Ts.length = D.bounds.length) (l2 : Ts'.length = Delta'.length) (l3 : ps.length = es.length)
    (n1 : (dom D.bounds ++ dom Delta').Nodup) (n2 : (this :: ps.map VarDecl.x).Nodup)
    (g1 : GSubstDefined (dom D.bounds ++ dom Delta') e0) (g2 : VSubstDefined (this :: ps.map VarDecl.x) e0) :
    Step d (.superCall r (.cls D.C Ts) Ts' m es)
      ((e0.gsubst (bind (D.bounds ++ Delta') (toGs Ts ++ toGs Ts'))).vsubst
        ((this :: ps.map VarDecl.x).zip (toV r :: toVs es))) := by
  have h := Step.simpleFound (d := d) (D := D) (M := .mk Delta' T0 m ps e0) (v0 := toV r) (Gs := toGs Ts)
    (Gs' := toGs Ts') (vs := toVs es) (.dec hD) hM (freshM _) (by rw [tys_length h2, l1])
    (by rw [tys_length h3, l2]) n1 n2 (by rw [exprs_length h4, l3]) g1 g2 rfl
  rw [h1, h2, h3, h4] at h
  exact h

theorem sInner {d : Decls} {C C' : ClassName} {Fs : List Funnel} {Ts0 : List Ty} {es0 : List Expr}
    {Ms : List Method} {Delta' : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl} {e0 : Expr}
    {Ts : List Ty} {es : List Expr}
    (hM : List.Mem (Method.mk Delta' T0 m ps e0) Ms)
    (h1 : (toV (.newLocal C Fs C' Ts0 es0 Ms)).expr = .newLocal C Fs C' Ts0 es0 Ms)
    (h2 : GTy.tys (toGs Ts) = Ts) (h4 : Value.exprs (toVs es) = es)
    (l2 : Ts.length = Delta'.length) (l3 : ps.length = es.length)
    (n1 : (dom Delta').Nodup) (n2 : (this :: ps.map VarDecl.x).Nodup)
    (g1 : GSubstDefined (dom Delta') e0) (g2 : VSubstDefined (this :: ps.map VarDecl.x) e0) :
    Step d (.call (.newLocal C Fs C' Ts0 es0 Ms) Ts m es)
      ((e0.gsubst (bind Delta' (toGs Ts))).vsubst
        ((this :: ps.map VarDecl.x).zip (toV (.newLocal C Fs C' Ts0 es0 Ms) :: toVs es))) := by
  have h := Step.innerFound (d := d) (M := .mk Delta' T0 m ps e0) (v0 := toV (.newLocal C Fs C' Ts0 es0 Ms))
    (Gs' := toGs Ts) (vs := toVs es) rfl hM (freshM _) (by rw [tys_length h2, l2])
    (by rw [exprs_length h4, l3]) n1 n2 g1 g2 rfl
  rw [h1, h2, h4] at h
  exact h

theorem sSearch {d : Decls} {D : Dec} {r : Expr} {Ts Ts' : List Ty} {m : MethName} {es : List Expr}
    (hD : List.Mem D d) (hm : Not (List.Mem m (D.Ms.map Method.name))) (ho : Not (D.C = Object))
    (h1 : (toV r).expr = r) (h2 : GTy.tys (toGs Ts) = Ts) (h3 : GTy.tys (toGs Ts') = Ts')
    (h4 : Value.exprs (toVs es) = es) (l1 : Ts.length = D.bounds.length) :
    Step d (.superCall r (.cls D.C Ts) Ts' m es)
      (.superCall r (.cls D.C' (Ty.substList (bind D.bounds Ts) D.Ts)) Ts' m es) := by
  have h := Step.searchSuper (d := d) (D := D) (m := m) (v := toV r) (Gs := toGs Ts) (Gs' := toGs Ts')
    (vs := toVs es) (.dec hD) hm ho (by rw [tys_length h2, l1])
  rw [h1, h2, h3, h4] at h
  exact h

theorem sThen {d : Decls} {r : Expr} {C' : ClassName} {Ts Ts' : List Ty} {x : VarName} {e1 e2 : Expr}
    (h1 : (toV r).expr = r) (hs : Sub d [] (typeOf (toV r)) (.cls C' Ts')) (hd : VSubstDefined [x] e1) :
    Step d (.ifInst r (.cls C' Ts) x e1 e2) (e1.vsubst [(x, toV r)]) := by
  have h := Step.ifThen (d := d) (v := toV r) (Ts := Ts) (e2 := e2) hs (Fresh.refl e1) hd
  rw [h1] at h
  exact h

theorem sElse {d : Decls} {r : Expr} {C' : ClassName} {Ts : List Ty} {x : VarName} {e1 e2 : Expr}
    (h1 : (toV r).expr = r) (hs : Not (exists Ts', Sub d [] (typeOf (toV r)) (.cls C' Ts'))) :
    Step d (.ifInst r (.cls C' Ts) x e1 e2) e2 := by
  have h := Step.ifElse (d := d) (v := toV r) (Ts := Ts) (x := x) (e1 := e1) (e2 := e2) hs
  rw [h1] at h
  exact h

theorem cRecv {d : Decls} {e e' : Expr} {Ts : List Ty} {m : MethName} {es : List Expr} (h : Step d e e')
    (h2 : GTy.tys (toGs Ts) = Ts) : Step d (.call e Ts m es) (.call e' Ts m es) := by
  have h' := Step.ctx (E := .callRecv .hole (toGs Ts) m es) h
  simp only [ECtx.plug] at h'
  rw [h2] at h'
  exact h'

theorem cArg0 {d : Decls} {r e e' : Expr} {Ts : List Ty} {m : MethName} {es : List Expr} (h : Step d e e')
    (h1 : (toV r).expr = r) (h2 : GTy.tys (toGs Ts) = Ts) : Step d (.call r Ts m (e :: es)) (.call r Ts m (e' :: es)) := by
  have h' := Step.ctx (E := .callArg (toV r) (toGs Ts) m [] .hole es) h
  simp only [ECtx.plug, Value.exprs, List.nil_append] at h'
  rw [h1, h2] at h'
  exact h'

theorem red {d : Decls} {e e' : Expr} (h : Step d e e') (hw : WFExpr e') : Reduces d e e' := And.intro h hw

theorem noValSuper {e : Expr} {T : Ty} {Ts : List Ty} {m : MethName} {es : List Expr} :
    Not (IsValue (.superCall e T Ts m es)) := by
  intro h
  cases h with
  | intro v hv => cases v <;> simp [Value.expr] at hv

theorem noValField {e : Expr} {f : FieldName} : Not (IsValue (.field e f)) := by
  intro h
  cases h with
  | intro v hv => cases v <;> simp [Value.expr] at hv

theorem noStepSuper {d : Decls} (hObj : forall D, List.Mem D d -> D.C = Object -> D.Ms.isEmpty = true) {v : Value}
    {m : MethName} : forall {e e' : Expr}, Step d e e' -> e = .superCall v.expr (.cls Object []) [] m [] -> False := by
  intro e e' h
  induction h with
  | @simpleFound D M _ _ _ _ _ _ _ _ _ _ hD hM =>
    intro he
    simp only [Expr.superCall.injEq, Ty.cls.injEq] at he
    have h0 := hObj _ hD.dec_mem he.2.1.1
    cases hMs : D.Ms with
    | nil => rw [hMs] at hM; cases hM
    | cons => rw [hMs] at h0; simp at h0
  | searchSuper _ _ ho =>
    intro he
    simp only [Expr.superCall.injEq, Ty.cls.injEq] at he
    exact ho he.2.1.1
  | @ctx E a b h ih =>
    intro he
    cases E with
    | hole => exact ih he
    | superRecv E' =>
      simp only [ECtx.plug, Expr.superCall.injEq] at he
      cases ECtx.plug_value he.1 with
      | intro v' hv' => exact Step.not_value h v' hv'
    | superArg =>
      simp only [ECtx.plug, Expr.superCall.injEq] at he
      simp at he
    | _ => simp only [ECtx.plug] at he; cases he
  | _ => intro he; cases he

theorem noStepField {d : Decls} {f : FieldName} : forall {e e' : Expr}, Step d e e' ->
    e = .field (.new Object [] []) f -> False := by
  intro e e' h
  induction h with
  | @simpleFieldFound D f' Gs vs1 vs v _ hl hm =>
    intro he
    simp only [Value.expr, Expr.field.injEq, Expr.new.injEq] at he
    have h1 : vs1 = [] := by
      have h2 := he.1.2.2
      rw [Value.exprs_eq_map] at h2
      simp at h2
      exact h2.1
    subst h1
    simp at hm
    cases hm
  | simpleFieldSuper _ _ _ ho =>
    intro he
    simp only [Value.expr, Expr.field.injEq, Expr.new.injEq] at he
    exact ho he.1.1
  | @ctx E a b h ih =>
    intro he
    cases E with
    | hole => exact ih he
    | field E' =>
      simp only [ECtx.plug, Expr.field.injEq] at he
      cases ECtx.plug_value (v := .new Object [] []) he.1 with
      | intro v' hv' => exact Step.not_value h v' hv'
    | _ => simp only [ECtx.plug] at he; cases he
  | _ => intro he; cases he

theorem stuckS {d : Decls} (hObj : forall D, List.Mem D d -> D.C = Object -> D.Ms.isEmpty = true) {v : Value}
    {m : MethName} : Not (IsValue (.superCall v.expr (.cls Object []) [] m [])) /\
      forall e', Not (Reduces d (.superCall v.expr (.cls Object []) [] m []) e') :=
  And.intro noValSuper (fun _ h => noStepSuper hObj h.1 rfl)

theorem subNames {d : Decls} {N : List ClassName}
    (hN : forall k, List.Mem k (classes d) -> List.Mem k.name N -> List.Mem k.sup N) {Delta : Bounds} {S T : Ty}
    (h : Sub d Delta S T) : forall {C Ts}, S = .cls C Ts -> List.Mem C N ->
      exists C' Ts', T = .cls C' Ts' /\ List.Mem C' N := by
  induction h with
  | subRefl => intro C Ts hS hC; exact Exists.intro C (Exists.intro Ts (And.intro hS hC))
  | @subInherit D Ts0 T' hD _ _ ih =>
    intro C Ts hS hC
    injection hS with hC' _
    subst hC'
    exact ih rfl (hN (.dec D) hD.mem hC)
  | @subInheritLocal C0 Fs C' Ts' es Ms Ts T' hD _ _ ih =>
    intro C Ts hS hC
    injection hS with hC' _
    subst hC'
    exact ih rfl (hN (.loc C0 Fs C' Ts' es Ms) hD.mem hC)
  | subVar _ _ _ => intro C Ts hS; cases hS

theorem notSub {d : Decls} (N : List ClassName)
    (hN : forall k, List.Mem k (classes d) -> List.Mem k.name N -> List.Mem k.sup N) {Delta : Bounds}
    {C C' : ClassName} {Ts Ts' : List Ty} (hC : List.Mem C N) (hC' : Not (List.Mem C' N)) :
    Not (Sub d Delta (.cls C Ts) (.cls C' Ts')) := by
  intro h
  cases subNames hN h rfl hC with
  | intro C1 h1 =>
    cases h1 with
    | intro Ts1 h2 =>
      injection h2.1 with e
      subst e
      exact hC' h2.2

theorem noSubEx {d : Decls} (N : List ClassName)
    (hN : forall k, List.Mem k (classes d) -> List.Mem k.name N -> List.Mem k.sup N) {Delta : Bounds}
    {C C' : ClassName} {Ts : List Ty} (hC : List.Mem C N) (hC' : Not (List.Mem C' N)) :
    Not (exists Ts', Sub d Delta (.cls C Ts) (.cls C' Ts')) := by
  intro h
  cases h with
  | intro Ts' h => exact notSub N hN hC hC' h

end Funnelling.ExampleFacts
