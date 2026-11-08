import Funnelling.Sound.Basic

open Funnelling.SoundSimp

namespace Funnelling

abbrev NonValue (a : Expr) : Prop := forall v : Value, Not (a = v.expr)

theorem ECtx.plug_nonvalue {E : ECtx} {a : Expr} (ha : NonValue a) : NonValue (E.plug a) := by
  intro v hv
  rcases ECtx.plug_value hv with ⟨v', hv'⟩; exact ha v' hv'

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
    (ihb : forall (E : ECtx) (a : Expr), b = E.plug a -> NonValue a ->
      exists a2, Step d a a2 /\ b2 = E.plug a2) :
    forall (E2 E : ECtx) (a : Expr), E2.plug b = E.plug a -> NonValue a ->
      exists a2, Step d a a2 /\ E2.plug b2 = E.plug a2 := by
  intro E2
  induction E2 with
  | hole => intro E a h ha; exact ihb E a h ha
  | callRecv E2 Gs m es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [ECtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .callRecv E2 Gs m es) hb) rfl)
    | callRecv E Gs' m' es' =>
      simp only [ECtx.plug, Expr.call.injEq] at h
      rcases ih E a h.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [ECtx.plug]; rw [h2.2, h.2.1, h.2.2.1, h.2.2.2]
    | callArg v Gs' m' vs E es' =>
      simp only [ECtx.plug, Expr.call.injEq] at h
      exact absurd h.1 (ECtx.plug_nonvalue hbn v)
    | _ => simp [ECtx.plug] at h
  | callArg v Gs m vs E2 es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [ECtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .callArg v Gs m vs E2 es) hb) rfl)
    | callRecv E Gs' m' es' =>
      simp only [ECtx.plug, Expr.call.injEq] at h
      exact absurd h.1.symm (ECtx.plug_nonvalue ha v)
    | callArg v' Gs' m' vs' E es' =>
      simp only [ECtx.plug, Expr.call.injEq] at h
      have r := exprs_split h.2.2.2 (ECtx.plug_nonvalue hbn) (ECtx.plug_nonvalue ha)
      rcases ih E a r.2.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [ECtx.plug]; rw [h2.2, Value.expr_inj h.1, GTy.tys_inj h.2.1, h.2.2.1, r.1, r.2.2]
    | _ => simp [ECtx.plug] at h
  | superRecv E2 G Gs m es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [ECtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .superRecv E2 G Gs m es) hb) rfl)
    | superRecv E G' Gs' m' es' =>
      simp only [ECtx.plug, Expr.superCall.injEq] at h
      rcases ih E a h.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [ECtx.plug]; rw [h2.2, GTy.ty_inj h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
    | superArg v G' Gs' m' vs E es' =>
      simp only [ECtx.plug, Expr.superCall.injEq] at h
      exact absurd h.1 (ECtx.plug_nonvalue hbn v)
    | _ => simp [ECtx.plug] at h
  | superArg v G Gs m vs E2 es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [ECtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .superArg v G Gs m vs E2 es) hb) rfl)
    | superRecv E G' Gs' m' es' =>
      simp only [ECtx.plug, Expr.superCall.injEq] at h
      exact absurd h.1.symm (ECtx.plug_nonvalue ha v)
    | superArg v' G' Gs' m' vs' E es' =>
      simp only [ECtx.plug, Expr.superCall.injEq] at h
      have r := exprs_split h.2.2.2.2 (ECtx.plug_nonvalue hbn) (ECtx.plug_nonvalue ha)
      rcases ih E a r.2.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [ECtx.plug]
      rw [h2.2, Value.expr_inj h.1, GTy.ty_inj h.2.1, GTy.tys_inj h.2.2.1, h.2.2.2.1, r.1, r.2.2]
    | _ => simp [ECtx.plug] at h
  | field E2 f ih =>
    intro E a h ha
    cases E with
    | hole => simp only [ECtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .field E2 f) hb) rfl)
    | field E f' =>
      simp only [ECtx.plug, Expr.field.injEq] at h
      rcases ih E a h.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [ECtx.plug]; rw [h2.2, h.2]
    | _ => simp [ECtx.plug] at h
  | newArg C Gs vs E2 es ih =>
    intro E a h ha
    cases E with
    | hole => simp only [ECtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .newArg C Gs vs E2 es) hb) rfl)
    | newArg C' Gs' vs' E es' =>
      simp only [ECtx.plug, Expr.new.injEq] at h
      have r := exprs_split h.2.2 (ECtx.plug_nonvalue hbn) (ECtx.plug_nonvalue ha)
      rcases ih E a r.2.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [ECtx.plug]; rw [h2.2, h.1, GTy.tys_inj h.2.1, r.1, r.2.2]
    | _ => simp [ECtx.plug] at h
  | localArg C Gs C' Gs' vs E2 es Ms ih =>
    intro E a h ha
    cases E with
    | hole => simp only [ECtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .localArg C Gs C' Gs' vs E2 es Ms) hb) rfl)
    | localArg D Hs D' Hs' vs' E es' Ms' =>
      simp only [ECtx.plug, Expr.newLocal.injEq] at h
      have r := exprs_split h.2.2.2.2.1 (ECtx.plug_nonvalue hbn) (ECtx.plug_nonvalue ha)
      have hG : Gs = Hs := by
        apply GTy.tys_inj
        rw [GTy.tys_eq_map, GTy.tys_eq_map]
        have := congrArg (List.map Funnel.abs) h.2.1
        simpa [List.map_map, Function.comp_def, Funnel.abs] using this
      rcases ih E a r.2.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [ECtx.plug]
      rw [h2.2, h.1, hG, h.2.2.1, GTy.tys_inj h.2.2.2.1, r.1, r.2.2, h.2.2.2.2.2]
    | _ => simp [ECtx.plug] at h
  | ifCond E2 G x e1 e2 ih =>
    intro E a h ha
    cases E with
    | hole => simp only [ECtx.plug] at h; subst h; exact Exists.intro _ (And.intro (Step.ctx (E := .ifCond E2 G x e1 e2) hb) rfl)
    | ifCond E G' x' e1' e2' =>
      simp only [ECtx.plug, Expr.ifInst.injEq] at h
      rcases ih E a h.1 ha with ⟨a2, h2⟩
      refine Exists.intro a2 (And.intro h2.1 ?_)
      simp only [ECtx.plug]; rw [h2.2, GTy.ty_inj h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
    | _ => simp [ECtx.plug] at h

theorem redex_field {E : ECtx} {a : Expr} {v : Value} {f : FieldName} (ha : NonValue a)
    (h : Expr.field v.expr f = E.plug a) (hE : Not (E = .hole)) : False := by
  cases E with
  | hole => exact hE rfl
  | field E f' =>
    simp only [ECtx.plug, Expr.field.injEq] at h
    exact ECtx.plug_nonvalue ha v h.1.symm
  | _ => simp [ECtx.plug] at h

theorem redex_if {E : ECtx} {a : Expr} {v : Value} {T : Ty} {x : VarName} {e1 e2 : Expr}
    (ha : NonValue a) (h : Expr.ifInst v.expr T x e1 e2 = E.plug a) (hE : Not (E = .hole)) : False := by
  cases E with
  | hole => exact hE rfl
  | ifCond E G x' e1' e2' =>
    simp only [ECtx.plug, Expr.ifInst.injEq] at h
    exact ECtx.plug_nonvalue ha v h.1.symm
  | _ => simp [ECtx.plug] at h

theorem redex_call {E : ECtx} {a : Expr} {v : Value} {Ts : List Ty} {m : MethName}
    {vs : List Value} (ha : NonValue a) (h : Expr.call v.expr Ts m (Value.exprs vs) = E.plug a)
    (hE : Not (E = .hole)) : False := by
  cases E with
  | hole => exact hE rfl
  | callRecv E Gs m' es =>
    simp only [ECtx.plug, Expr.call.injEq] at h
    exact ECtx.plug_nonvalue ha v h.1.symm
  | callArg v' Gs m' vs' E es =>
    simp only [ECtx.plug, Expr.call.injEq] at h
    rcases Value.exprs_append_cons h.2.2.2 with ⟨w, hw⟩; exact ECtx.plug_nonvalue ha w hw
  | _ => simp [ECtx.plug] at h

theorem redex_super {E : ECtx} {a : Expr} {v : Value} {T : Ty} {Ts : List Ty} {m : MethName}
    {vs : List Value} (ha : NonValue a) (h : Expr.superCall v.expr T Ts m (Value.exprs vs) = E.plug a)
    (hE : Not (E = .hole)) : False := by
  cases E with
  | hole => exact hE rfl
  | superRecv E G Gs m' es =>
    simp only [ECtx.plug, Expr.superCall.injEq] at h
    exact ECtx.plug_nonvalue ha v h.1.symm
  | superArg v' G Gs m' vs' E es =>
    simp only [ECtx.plug, Expr.superCall.injEq] at h
    rcases Value.exprs_append_cons h.2.2.2.2 with ⟨w, hw⟩; exact ECtx.plug_nonvalue ha w hw
  | _ => simp [ECtx.plug] at h

theorem Step.decompNonHole {d : Decls} {e e2 : Expr} (h : Step d e e2) :
    forall (E : ECtx) (a : Expr), e = E.plug a -> NonValue a -> Not (E = .hole) ->
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
    | hole => simp only [ECtx.plug] at h'; subst h'; exact Exists.intro _ (And.intro hb rfl)
    | _ => exact ih _ a' h' ha' (by simp)

theorem Step.decomp {d : Decls} {E : ECtx} {a e2 : Expr} (h : Step d (E.plug a) e2) (ha : NonValue a) :
    exists a2, Step d a a2 /\ e2 = E.plug a2 := by
  cases E with
  | hole => exact Exists.intro e2 (And.intro h rfl)
  | _ => exact Step.decompNonHole h _ a rfl ha (by simp)

end Funnelling
