import Funnelling.Sound.Lists

open Funnelling.SoundSimp

namespace Funnelling

theorem EvalCtx.plug_value {E : EvalCtx} {a : Expr} {v : Value} (h : E.plug a = v.expr) :
    exists v' : Value, a = v'.expr := by
  induction E generalizing v with
  | hole => exact Exists.intro v h
  | callRecv => cases v <;> simp [EvalCtx.plug, Value.expr] at h
  | callArg => cases v <;> simp [EvalCtx.plug, Value.expr] at h
  | superRecv => cases v <;> simp [EvalCtx.plug, Value.expr] at h
  | superArg => cases v <;> simp [EvalCtx.plug, Value.expr] at h
  | field => cases v <;> simp [EvalCtx.plug, Value.expr] at h
  | ifCond => cases v <;> simp [EvalCtx.plug, Value.expr] at h
  | newArg C Gs vs E es ih =>
    cases v with
    | new C' Gs' vs' =>
      simp only [EvalCtx.plug, Value.expr, Expr.new.injEq] at h
      rcases Value.exprs_append_cons h.2.2.symm with ⟨v1, hv1⟩; exact ih hv1
    | newLocal => simp [EvalCtx.plug, Value.expr] at h
  | newLocalArg C Gs C' Gs' vs E es Ms ih =>
    cases v with
    | new => simp [EvalCtx.plug, Value.expr] at h
    | newLocal D Hs D' Hs' ws Ns =>
      simp only [EvalCtx.plug, Value.expr, Expr.newLocal.injEq] at h
      rcases Value.exprs_append_cons h.2.2.2.2.1.symm with ⟨v1, hv1⟩; exact ih hv1

theorem Step.not_value {d : Decls} {e e' : Expr} (h : Step d e e') :
    forall v : Value, Not (e = v.expr) := by
  induction h with
  | simpleFieldFound => intro v hv; cases v <;> simp [Value.expr] at hv
  | simpleFieldSuper => intro v hv; cases v <;> simp [Value.expr] at hv
  | innerFieldSuper => intro v hv; cases v <;> simp [Value.expr] at hv
  | ifThen => intro v hv; cases v <;> simp [Value.expr] at hv
  | ifElse => intro v hv; cases v <;> simp [Value.expr] at hv
  | simpleAddSuper => intro v hv; cases v <;> simp [Value.expr] at hv
  | simpleFound => intro v hv; cases v <;> simp [Value.expr] at hv
  | innerFound => intro v hv; cases v <;> simp [Value.expr] at hv
  | innerSuper => intro v hv; cases v <;> simp [Value.expr] at hv
  | searchSuper => intro v hv; cases v <;> simp [Value.expr] at hv
  | ctx _ ih =>
    intro v hv
    rcases EvalCtx.plug_value hv with ⟨v', hv'⟩; exact ih v' hv'

abbrev NonValue (a : Expr) : Prop := forall v : Value, Not (a = v.expr)

theorem EvalCtx.plug_nonvalue {E : EvalCtx} {a : Expr} (ha : NonValue a) : NonValue (E.plug a) := by
  intro v hv
  rcases EvalCtx.plug_value hv with ⟨v', hv'⟩; exact ha v' hv'

theorem exprs_split {vs1 vs2 : List Value} {x y : Expr} {es1 es2 : List Expr}
    (h : Value.exprs vs1 ++ x :: es1 = Value.exprs vs2 ++ y :: es2) (hx : NonValue x)
    (hy : NonValue y) : vs1 = vs2 /\ x = y /\ es1 = es2 := by
  induction vs1 generalizing vs2 with
  | nil =>
    cases vs2 with
    | nil =>
      simp_all
    | cons v vs2 =>
      simp only [Value.exprs, List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (hx v)
  | cons v vs1 ih =>
    cases vs2 with
    | nil =>
      simp only [Value.exprs, List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm (hy v)
    | cons w vs2 =>
      simp only [Value.exprs, List.cons_append, List.cons.injEq] at h
      have r := ih h.2
      exact And.intro (by rw [Value.expr_inj h.1, r.1]) r.2

theorem Step.decompAux {d : Decls} {b b2 : Expr} (hb : Step d b b2) (hbn : NonValue b)
    (ihb : forall (E : EvalCtx) (a : Expr), b = E.plug a -> NonValue a ->
      exists a2, Step d a a2 /\ b2 = E.plug a2) :
    forall (E2 E : EvalCtx) (a : Expr), E2.plug b = E.plug a -> NonValue a ->
      exists a2, Step d a a2 /\ E2.plug b2 = E.plug a2 := by
  intro E2
  induction E2 with
  | hole => intro E a h ha; exact ihb E a h ha
  | callRecv E2 Gs m es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [EvalCtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .callRecv E2 Gs m es) hb) rfl)
    | callRecv E Gs' m' es' =>
      simp only [EvalCtx.plug, Expr.call.injEq] at h
      rcases ih E a h.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [EvalCtx.plug]; rw [h2.2, h.2.1, h.2.2.1, h.2.2.2]
    | callArg v Gs' m' vs E es' =>
      simp only [EvalCtx.plug, Expr.call.injEq] at h
      exact absurd h.1 (EvalCtx.plug_nonvalue hbn v)
    | _ => simp [EvalCtx.plug] at h
  | callArg v Gs m vs E2 es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [EvalCtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .callArg v Gs m vs E2 es) hb) rfl)
    | callRecv E Gs' m' es' =>
      simp only [EvalCtx.plug, Expr.call.injEq] at h
      exact absurd h.1.symm (EvalCtx.plug_nonvalue ha v)
    | callArg v' Gs' m' vs' E es' =>
      simp only [EvalCtx.plug, Expr.call.injEq] at h
      have r := exprs_split h.2.2.2 (EvalCtx.plug_nonvalue hbn) (EvalCtx.plug_nonvalue ha)
      rcases ih E a r.2.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [EvalCtx.plug]; rw [h2.2, Value.expr_inj h.1, GTy.tys_inj h.2.1, h.2.2.1, r.1, r.2.2]
    | _ => simp [EvalCtx.plug] at h
  | superRecv E2 G Gs m es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [EvalCtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .superRecv E2 G Gs m es) hb) rfl)
    | superRecv E G' Gs' m' es' =>
      simp only [EvalCtx.plug, Expr.superCall.injEq] at h
      rcases ih E a h.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [EvalCtx.plug]; rw [h2.2, GTy.ty_inj h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
    | superArg v G' Gs' m' vs E es' =>
      simp only [EvalCtx.plug, Expr.superCall.injEq] at h
      exact absurd h.1 (EvalCtx.plug_nonvalue hbn v)
    | _ => simp [EvalCtx.plug] at h
  | superArg v G Gs m vs E2 es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [EvalCtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .superArg v G Gs m vs E2 es) hb) rfl)
    | superRecv E G' Gs' m' es' =>
      simp only [EvalCtx.plug, Expr.superCall.injEq] at h
      exact absurd h.1.symm (EvalCtx.plug_nonvalue ha v)
    | superArg v' G' Gs' m' vs' E es' =>
      simp only [EvalCtx.plug, Expr.superCall.injEq] at h
      have r := exprs_split h.2.2.2.2 (EvalCtx.plug_nonvalue hbn) (EvalCtx.plug_nonvalue ha)
      rcases ih E a r.2.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [EvalCtx.plug]
      rw [h2.2, Value.expr_inj h.1, GTy.ty_inj h.2.1, GTy.tys_inj h.2.2.1, h.2.2.2.1, r.1, r.2.2]
    | _ => simp [EvalCtx.plug] at h
  | field E2 f ih =>
    intro E a h ha
    cases E with
    | hole => simp only [EvalCtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .field E2 f) hb) rfl)
    | field E f' =>
      simp only [EvalCtx.plug, Expr.field.injEq] at h
      rcases ih E a h.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [EvalCtx.plug]; rw [h2.2, h.2]
    | _ => simp [EvalCtx.plug] at h
  | newArg C Gs vs E2 es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [EvalCtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .newArg C Gs vs E2 es) hb) rfl)
    | newArg C' Gs' vs' E es' =>
      simp only [EvalCtx.plug, Expr.new.injEq] at h
      have r := exprs_split h.2.2 (EvalCtx.plug_nonvalue hbn) (EvalCtx.plug_nonvalue ha)
      rcases ih E a r.2.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [EvalCtx.plug]; rw [h2.2, h.1, GTy.tys_inj h.2.1, r.1, r.2.2]
    | _ => simp [EvalCtx.plug] at h
  | newLocalArg C Gs C' Gs' vs E2 es Ms ih =>
    intro E a h ha
    cases E with
    | hole => simp only [EvalCtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .newLocalArg C Gs C' Gs' vs E2 es Ms) hb) rfl)
    | newLocalArg D Hs D' Hs' vs' E es' Ms' =>
      simp only [EvalCtx.plug, Expr.newLocal.injEq] at h
      have r := exprs_split h.2.2.2.2.1 (EvalCtx.plug_nonvalue hbn) (EvalCtx.plug_nonvalue ha)
      have hG : Gs = Hs := by
        apply GTy.tys_inj
        rw [GTy.tys_eq_map, GTy.tys_eq_map]
        have := congrArg (List.map Funnel.abs) h.2.1
        simpa [List.map_map, Function.comp_def, Funnel.abs] using this
      rcases ih E a r.2.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [EvalCtx.plug]
      rw [h2.2, h.1, hG, h.2.2.1, GTy.tys_inj h.2.2.2.1, r.1, r.2.2, h.2.2.2.2.2]
    | _ => simp [EvalCtx.plug] at h
  | ifCond E2 G x e1 e2 ih =>
    intro E a h ha
    cases E with
    | hole => simp only [EvalCtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .ifCond E2 G x e1 e2) hb) rfl)
    | ifCond E G' x' e1' e2' =>
      simp only [EvalCtx.plug, Expr.ifInst.injEq] at h
      rcases ih E a h.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [EvalCtx.plug]; rw [h2.2, GTy.ty_inj h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
    | _ => simp [EvalCtx.plug] at h

theorem redex_field {E : EvalCtx} {a : Expr} {v : Value} {f : FieldName} (ha : NonValue a)
    (h : Expr.field v.expr f = E.plug a) (hE : Not (E = .hole)) : False := by
  cases E with
  | hole => exact hE rfl
  | field E f' =>
    simp only [EvalCtx.plug, Expr.field.injEq] at h
    exact EvalCtx.plug_nonvalue ha v h.1.symm
  | _ => simp [EvalCtx.plug] at h

theorem redex_if {E : EvalCtx} {a : Expr} {v : Value} {T : Ty} {x : VarName} {e1 e2 : Expr}
    (ha : NonValue a) (h : Expr.ifInst v.expr T x e1 e2 = E.plug a) (hE : Not (E = .hole)) : False := by
  cases E with
  | hole => exact hE rfl
  | ifCond E G x' e1' e2' =>
    simp only [EvalCtx.plug, Expr.ifInst.injEq] at h
    exact EvalCtx.plug_nonvalue ha v h.1.symm
  | _ => simp [EvalCtx.plug] at h

theorem redex_call {E : EvalCtx} {a : Expr} {v : Value} {Ts : List Ty} {m : MethName}
    {vs : List Value} (ha : NonValue a) (h : Expr.call v.expr Ts m (Value.exprs vs) = E.plug a)
    (hE : Not (E = .hole)) : False := by
  cases E with
  | hole => exact hE rfl
  | callRecv E Gs m' es =>
    simp only [EvalCtx.plug, Expr.call.injEq] at h
    exact EvalCtx.plug_nonvalue ha v h.1.symm
  | callArg v' Gs m' vs' E es =>
    simp only [EvalCtx.plug, Expr.call.injEq] at h
    rcases Value.exprs_append_cons h.2.2.2 with ⟨w, hw⟩; exact EvalCtx.plug_nonvalue ha w hw
  | _ => simp [EvalCtx.plug] at h

theorem redex_super {E : EvalCtx} {a : Expr} {v : Value} {T : Ty} {Ts : List Ty} {m : MethName}
    {vs : List Value} (ha : NonValue a) (h : Expr.superCall v.expr T Ts m (Value.exprs vs) = E.plug a)
    (hE : Not (E = .hole)) : False := by
  cases E with
  | hole => exact hE rfl
  | superRecv E G Gs m' es =>
    simp only [EvalCtx.plug, Expr.superCall.injEq] at h
    exact EvalCtx.plug_nonvalue ha v h.1.symm
  | superArg v' G Gs m' vs' E es =>
    simp only [EvalCtx.plug, Expr.superCall.injEq] at h
    rcases Value.exprs_append_cons h.2.2.2.2 with ⟨w, hw⟩; exact EvalCtx.plug_nonvalue ha w hw
  | _ => simp [EvalCtx.plug] at h

theorem Step.decompNonHole {d : Decls} {e e2 : Expr} (h : Step d e e2) :
    forall (E : EvalCtx) (a : Expr), e = E.plug a -> NonValue a -> Not (E = .hole) ->
      exists a2, Step d a a2 /\ e2 = E.plug a2 := by
  induction h with
  | simpleFieldFound => intro E a h ha hE; exact absurd (redex_field ha h hE) id
  | simpleFieldSuper => intro E a h ha hE; exact absurd (redex_field ha h hE) id
  | innerFieldSuper => intro E a h ha hE; exact absurd (redex_field ha h hE) id
  | ifThen => intro E a h ha hE; exact absurd (redex_if ha h hE) id
  | ifElse => intro E a h ha hE; exact absurd (redex_if ha h hE) id
  | simpleAddSuper => intro E a h ha hE; exact absurd (redex_call ha h hE) id
  | simpleFound => intro E a h ha hE; exact absurd (redex_super ha h hE) id
  | innerFound => intro E a h ha hE; exact absurd (redex_call ha h hE) id
  | innerSuper => intro E a h ha hE; exact absurd (redex_call ha h hE) id
  | searchSuper => intro E a h ha hE; exact absurd (redex_super ha h hE) id
  | ctx hb ih =>
    intro E a h ha _
    refine Step.decompAux hb (Step.not_value hb) ?_ _ E a h ha
    intro E' a' h' ha'
    cases E' with
    | hole => simp only [EvalCtx.plug] at h'; subst h'; exact Exists.intro _ (And.intro hb rfl)
    | _ => exact ih _ a' h' ha' (by simp)

theorem Step.decomp {d : Decls} {E : EvalCtx} {a e2 : Expr} (h : Step d (E.plug a) e2) (ha : NonValue a) :
    exists a2, Step d a a2 /\ e2 = E.plug a2 := by
  cases E with
  | hole => exact Exists.intro e2 (And.intro h rfl)
  | _ => exact Step.decompNonHole h _ a rfl ha (by simp)

inductive BaseStep (d : Decls) : Expr -> Expr -> Prop
  | simpleFieldFound {D f} {Gs : List GTy} {vs1 vs : List Value} {v : Value} :
      Declared d (.dec D) ->
      vs1.length = D.Ss.length ->
      List.Mem (f, v) ((D.Ss.map Slot.f).zip vs1) ->
      BaseStep d (.field (Value.new D.C Gs (vs1 ++ vs)) f) v
  | simpleFieldSuper {D f} {Gs : List GTy} {vs1 vs : List Value} :
      Declared d (.dec D) ->
      vs1.length = D.Ss.length ->
      Not (List.Mem f (D.Ss.map Slot.f)) ->
      Not (D.C = Object) ->
      Gs.length = D.Delta.length ->
      BaseStep d (.field (Value.new D.C Gs (vs1 ++ vs)) f)
        (.field (.new D.C' (Ty.substList (bind D.Delta (Gs : List Ty)) D.Ts) vs) f)
  | innerFieldSuper {C C' Ms f} {Gs Gs' : List GTy} {vs : List Value} :
      BaseStep d (.field (Value.newLocal C Gs C' Gs' vs Ms) f) (.field (Value.new C' Gs' vs) f)
  | ifThen {C' Ts Ts' x e1 e1' e2} {v : Value} :
      Sub d [] (typeOf v) (.cls C' Ts') ->
      Fresh e1 e1' ->
      VSubstDefined [x] e1' ->
      BaseStep d (.ifInst v (.cls C' Ts) x e1 e2) (e1'.vsubst [(x, v)])
  | ifElse {C' Ts x e1 e2} {v : Value} :
      Not (exists Ts', Sub d [] (typeOf v) (.cls C' Ts')) ->
      BaseStep d (.ifInst v (.cls C' Ts) x e1 e2) e2
  | simpleAddSuper {C m} {v : Value} {Gs Gs' : List GTy} {vs0 vs : List Value} :
      v = Value.new C Gs vs0 ->
      BaseStep d (.call v Gs' m vs) (.superCall v (.cls C Gs) Gs' m vs)
  | simpleFound {D M m Delta' T0 ps e0 e} {v0 : Value} {Gs Gs' : List GTy} {vs : List Value} :
      Declared d (.dec D) ->
      List.Mem M D.Ms ->
      FreshM M (.mk Delta' T0 m ps e0) ->
      Gs.length = D.Delta.length -> Gs'.length = Delta'.length ->
      (dom D.Delta ++ dom Delta').Nodup ->
      (this :: ps.map VarDecl.x).Nodup ->
      ps.length = vs.length ->
      GSubstDefined (dom D.Delta ++ dom Delta') e0 ->
      VSubstDefined (this :: ps.map VarDecl.x) e0 ->
      e = (e0.gsubst (bind (D.Delta ++ Delta') (Gs ++ Gs'))).vsubst
        ((this :: ps.map VarDecl.x).zip (v0 :: vs)) ->
      BaseStep d (.superCall v0 (.cls D.C Gs) Gs' m vs) e
  | innerFound {C C' Ms M m Delta' T0 ps e0 e} {v0 : Value} {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} :
      v0 = Value.newLocal C Gs C' Gs'' vs0 Ms ->
      List.Mem M Ms ->
      FreshM M (.mk Delta' T0 m ps e0) ->
      Gs'.length = Delta'.length ->
      ps.length = vs.length ->
      (dom Delta').Nodup ->
      (this :: ps.map VarDecl.x).Nodup ->
      GSubstDefined (dom Delta') e0 ->
      VSubstDefined (this :: ps.map VarDecl.x) e0 ->
      e = (e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs)) ->
      BaseStep d (.call v0 Gs' m vs) e
  | innerSuper {C C' Ms m} {v0 : Value} {Gs0 Gs Gs' : List GTy} {vs0 vs : List Value} :
      v0 = Value.newLocal C Gs0 C' Gs vs0 Ms ->
      Not (List.Mem m (Ms.map Method.name)) ->
      BaseStep d (.call v0 Gs' m vs) (.superCall v0 (.cls C' Gs) Gs' m vs)
  | searchSuper {D m} {v : Value} {Gs Gs' : List GTy} {vs : List Value} :
      Declared d (.dec D) ->
      Not (List.Mem m (D.Ms.map Method.name)) ->
      Not (D.C = Object) ->
      Gs.length = D.Delta.length ->
      BaseStep d (.superCall v (.cls D.C Gs) Gs' m vs)
        (.superCall v (.cls D.C' (Ty.substList (bind D.Delta (Gs : List Ty)) D.Ts)) Gs' m vs)

theorem BaseStep.toStep {d : Decls} {e e' : Expr} (h : BaseStep d e e') : Step d e e' := by
  cases h with
  | simpleFieldFound h1 h2 h3 => exact Step.simpleFieldFound h1 h2 h3
  | simpleFieldSuper h1 h2 h3 h4 h5 => exact Step.simpleFieldSuper h1 h2 h3 h4 h5
  | innerFieldSuper => exact Step.innerFieldSuper
  | ifThen h1 h2 h3 => exact Step.ifThen h1 h2 h3
  | ifElse h1 => exact Step.ifElse h1
  | simpleAddSuper h1 => exact Step.simpleAddSuper h1
  | simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => exact Step.simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact Step.innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | innerSuper h1 h2 => exact Step.innerSuper h1 h2
  | searchSuper h1 h2 h3 h4 => exact Step.searchSuper h1 h2 h3 h4

theorem BaseStep.nonhole {d : Decls} {e e' : Expr} (h : BaseStep d e e') {E : EvalCtx} {c : Expr}
    (hE : E.plug c = e) (hne : Not (E = .hole)) (hc : NonValue c) : False := by
  cases h with
  | simpleFieldFound => exact redex_field hc hE.symm hne
  | simpleFieldSuper => exact redex_field hc hE.symm hne
  | innerFieldSuper => exact redex_field hc hE.symm hne
  | ifThen => exact redex_if hc hE.symm hne
  | ifElse => exact redex_if hc hE.symm hne
  | simpleAddSuper => exact redex_call hc hE.symm hne
  | simpleFound => exact redex_super hc hE.symm hne
  | innerFound => exact redex_call hc hE.symm hne
  | innerSuper => exact redex_call hc hE.symm hne
  | searchSuper => exact redex_super hc hE.symm hne

theorem Step.strip {d : Decls} {a b2 : Expr} (h2 : Step d a b2) :
    forall {b1 : Expr}, BaseStep d a b1 -> BaseStep d a b2 := by
  induction h2 with
  | simpleFieldFound h1 h2 h3 => intro _ _; exact BaseStep.simpleFieldFound h1 h2 h3
  | simpleFieldSuper h1 h2 h3 h4 h5 => intro _ _; exact BaseStep.simpleFieldSuper h1 h2 h3 h4 h5
  | innerFieldSuper => intro _ _; exact BaseStep.innerFieldSuper
  | ifThen h1 h2 h3 => intro _ _; exact BaseStep.ifThen h1 h2 h3
  | ifElse h1 => intro _ _; exact BaseStep.ifElse h1
  | simpleAddSuper h1 => intro _ _; exact BaseStep.simpleAddSuper h1
  | simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    intro _ _; exact BaseStep.simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    intro _ _; exact BaseStep.innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | innerSuper h1 h2 => intro _ _; exact BaseStep.innerSuper h1 h2
  | searchSuper h1 h2 h3 h4 => intro _ _; exact BaseStep.searchSuper h1 h2 h3 h4
  | @ctx E c c2 hc ih =>
    intro b1 hb
    cases E with
    | hole => exact ih hb
    | _ => exact absurd (hb.nonhole rfl (by simp) (Step.not_value hc)) id

def EvalCtx.comp : EvalCtx -> EvalCtx -> EvalCtx
  | .hole, E' => E'
  | .callRecv E Gs m es, E' => .callRecv (E.comp E') Gs m es
  | .callArg v Gs m vs E es, E' => .callArg v Gs m vs (E.comp E') es
  | .superRecv E G Gs m es, E' => .superRecv (E.comp E') G Gs m es
  | .superArg v G Gs m vs E es, E' => .superArg v G Gs m vs (E.comp E') es
  | .field E f, E' => .field (E.comp E') f
  | .newArg C Gs vs E es, E' => .newArg C Gs vs (E.comp E') es
  | .newLocalArg C Gs C' Gs' vs E es Ms, E' => .newLocalArg C Gs C' Gs' vs (E.comp E') es Ms
  | .ifCond E G x e1 e2, E' => .ifCond (E.comp E') G x e1 e2

theorem EvalCtx.comp_plug : forall (E E' : EvalCtx) (a : Expr), (E.comp E').plug a = E.plug (E'.plug a)
  | .hole, _, _ => rfl
  | .callRecv E _ _ _, E', a => by simp only [EvalCtx.comp, EvalCtx.plug, EvalCtx.comp_plug E E' a]
  | .callArg _ _ _ _ E _, E', a => by simp only [EvalCtx.comp, EvalCtx.plug, EvalCtx.comp_plug E E' a]
  | .superRecv E _ _ _ _, E', a => by simp only [EvalCtx.comp, EvalCtx.plug, EvalCtx.comp_plug E E' a]
  | .superArg _ _ _ _ _ E _, E', a => by simp only [EvalCtx.comp, EvalCtx.plug, EvalCtx.comp_plug E E' a]
  | .field E _, E', a => by simp only [EvalCtx.comp, EvalCtx.plug, EvalCtx.comp_plug E E' a]
  | .newArg _ _ _ E _, E', a => by simp only [EvalCtx.comp, EvalCtx.plug, EvalCtx.comp_plug E E' a]
  | .newLocalArg _ _ _ _ _ E _ _, E', a => by simp only [EvalCtx.comp, EvalCtx.plug, EvalCtx.comp_plug E E' a]
  | .ifCond E _ _ _ _, E', a => by simp only [EvalCtx.comp, EvalCtx.plug, EvalCtx.comp_plug E E' a]

theorem Step.toBase {d : Decls} {e e' : Expr} (h : Step d e e') :
    exists (E : EvalCtx) (a a' : Expr), e = E.plug a /\ e' = E.plug a' /\ BaseStep d a a' := by
  induction h with
  | simpleFieldFound h1 h2 h3 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.simpleFieldFound h1 h2 h3)))))
  | simpleFieldSuper h1 h2 h3 h4 h5 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.simpleFieldSuper h1 h2 h3 h4 h5)))))
  | innerFieldSuper =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl BaseStep.innerFieldSuper))))
  | ifThen h1 h2 h3 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.ifThen h1 h2 h3)))))
  | ifElse h1 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.ifElse h1)))))
  | simpleAddSuper h1 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.simpleAddSuper h1)))))
  | simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl
      (BaseStep.simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)))))
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl
      (BaseStep.innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)))))
  | innerSuper h1 h2 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.innerSuper h1 h2)))))
  | searchSuper h1 h2 h3 h4 =>
    exact Exists.intro EvalCtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.searchSuper h1 h2 h3 h4)))))
  | @ctx E c c2 _ ih =>
    rcases ih with ⟨E', h'⟩
    rcases h' with ⟨a, h'⟩
    rcases h' with ⟨a', h'⟩
    refine Exists.intro (E.comp E') (Exists.intro a (Exists.intro a' (And.intro ?_ (And.intro ?_ h'.2.2))))
    . rw [EvalCtx.comp_plug, h'.1]
    . rw [EvalCtx.comp_plug, h'.2.1]

end Funnelling
