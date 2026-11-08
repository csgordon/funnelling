import Funnelling.Reduction

namespace Funnelling.SoundSimp

@[scoped simp] theorem listMem_iff {A : Type} {x : A} {l : List A} : List.Mem x l <-> Membership.mem l x := Iff.rfl

end Funnelling.SoundSimp

open Funnelling.SoundSimp

namespace Funnelling

theorem GTy.tys_eq_map : forall Gs : List GTy, GTy.tys Gs = Gs.map GTy.ty
  | [] => rfl
  | G :: Gs => by simp [GTy.tys, GTy.tys_eq_map Gs]

theorem Value.exprs_eq_map : forall vs : List Value, Value.exprs vs = vs.map Value.expr
  | [] => rfl
  | v :: vs => by simp [Value.exprs, Value.exprs_eq_map vs]

mutual
theorem GTy.ty_inj : forall {G G' : GTy}, G.ty = G'.ty -> G = G'
  | .cls C Gs, .cls C' Gs', h => by
    simp only [GTy.ty, Ty.cls.injEq] at h
    rw [h.1, GTy.tys_inj h.2]
theorem GTy.tys_inj : forall {Gs Gs' : List GTy}, GTy.tys Gs = GTy.tys Gs' -> Gs = Gs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [GTy.tys] at h
  | _ :: _, [], h => by simp [GTy.tys] at h
  | G :: Gs, G' :: Gs', h => by
    simp only [GTy.tys, List.cons.injEq] at h
    rw [GTy.ty_inj h.1, GTy.tys_inj h.2]
end

mutual
theorem Value.expr_inj : forall {v v' : Value}, v.expr = v'.expr -> v = v'
  | .new C Gs vs, .new C' Gs' vs', h => by
    simp only [Value.expr, Expr.new.injEq] at h
    rw [h.1, GTy.tys_inj h.2.1, Value.exprs_inj h.2.2]
  | .new _ _ _, .newLocal _ _ _ _ _ _, h => by simp [Value.expr] at h
  | .newLocal _ _ _ _ _ _, .new _ _ _, h => by simp [Value.expr] at h
  | .newLocal C Gs C' Gs' vs Ms, .newLocal D Hs D' Hs' ws Ns, h => by
    simp only [Value.expr, Expr.newLocal.injEq] at h
    have h2' : Gs = Hs := by
      apply GTy.tys_inj
      rw [GTy.tys_eq_map, GTy.tys_eq_map]
      have := congrArg (List.map Funnel.abs) h.2.1
      simpa [List.map_map, Function.comp_def, Funnel.abs] using this
    rw [h.1, h2', h.2.2.1, GTy.tys_inj h.2.2.2.1, Value.exprs_inj h.2.2.2.2.1, h.2.2.2.2.2]
theorem Value.exprs_inj : forall {vs vs' : List Value}, Value.exprs vs = Value.exprs vs' -> vs = vs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Value.exprs] at h
  | _ :: _, [], h => by simp [Value.exprs] at h
  | v :: vs, v' :: vs', h => by
    simp only [Value.exprs, List.cons.injEq] at h
    rw [Value.expr_inj h.1, Value.exprs_inj h.2]
end

theorem Value.mem_exprs {vs : List Value} {e : Expr} (h : List.Mem e (Value.exprs vs)) :
    exists v : Value, List.Mem v vs /\ e = v.expr := by
  rw [Value.exprs_eq_map] at h
  have h' := List.mem_map.mp h
  rcases h' with ⟨v, hv⟩; exact Exists.intro v (And.intro hv.1 hv.2.symm)

theorem Value.exprs_append_cons {vs : List Value} {es1 es2 : List Expr} {e : Expr}
    (h : Value.exprs vs = es1 ++ e :: es2) : exists v : Value, e = v.expr := by
  have hm : List.Mem e (Value.exprs vs) := by rw [h]; exact List.mem_append_right _ (List.Mem.head _)
  rcases Value.mem_exprs hm with ⟨v, hv⟩; exact Exists.intro v hv.2

theorem ECtx.plug_value {E : ECtx} {a : Expr} {v : Value} (h : E.plug a = v.expr) :
    exists v' : Value, a = v'.expr := by
  induction E generalizing v with
  | hole => exact Exists.intro v h
  | callRecv => cases v <;> simp [ECtx.plug, Value.expr] at h
  | callArg => cases v <;> simp [ECtx.plug, Value.expr] at h
  | superRecv => cases v <;> simp [ECtx.plug, Value.expr] at h
  | superArg => cases v <;> simp [ECtx.plug, Value.expr] at h
  | field => cases v <;> simp [ECtx.plug, Value.expr] at h
  | ifCond => cases v <;> simp [ECtx.plug, Value.expr] at h
  | newArg C Gs vs E es ih =>
    cases v with
    | new C' Gs' vs' =>
      simp only [ECtx.plug, Value.expr, Expr.new.injEq] at h
      rcases Value.exprs_append_cons h.2.2.symm with ⟨v1, hv1⟩; exact ih hv1
    | newLocal => simp [ECtx.plug, Value.expr] at h
  | localArg C Gs C' Gs' vs E es Ms ih =>
    cases v with
    | new => simp [ECtx.plug, Value.expr] at h
    | newLocal D Hs D' Hs' ws Ns =>
      simp only [ECtx.plug, Value.expr, Expr.newLocal.injEq] at h
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
    rcases ECtx.plug_value hv with ⟨v', hv'⟩; exact ih v' hv'

end Funnelling
