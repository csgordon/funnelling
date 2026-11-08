import Funnelling.Sound.CtxTyping

open Funnelling.SoundSimp

namespace Funnelling.High

abbrev LocClosed (L : List K) : Prop := forall k, List.Mem k L -> Sub1 (Method.localsList k.Ms) L

theorem LocClosed.append {L1 L2 : List K} (h1 : LocClosed L1) (h2 : LocClosed L2) : LocClosed (L1 ++ L2) := by
  intro k hk x hx
  simp only [listMem_iff, List.mem_append] at hk |-
  rcases hk with hk | hk
  . exact Or.inl (h1 k hk x hx)
  . exact Or.inr (h2 k hk x hx)

mutual
theorem Expr.locClosed : forall (e : Expr), LocClosed e.locals
  | .var _ => fun _ h => by cases h
  | .call e _ _ es => by simp only [Expr.locals]; exact (Expr.locClosed e).append (Expr.locClosedList es)
  | .superCall e _ _ _ es => by simp only [Expr.locals]; exact (Expr.locClosed e).append (Expr.locClosedList es)
  | .field e _ => by simp only [Expr.locals]; exact Expr.locClosed e
  | .new _ _ es => by simp only [Expr.locals]; exact Expr.locClosedList es
  | .newLocal C Fs C' Ts es Ms => by
    intro k hk x hx
    cases hk with
    | head => exact List.Mem.tail _ (List.mem_append_right _ hx)
    | tail _ hk =>
      exact List.Mem.tail _ (((Expr.locClosedList es).append (Method.locClosedList Ms)) k hk x hx)
  | .ifInst e0 _ _ e1 e2 => ((Expr.locClosed e0).append (Expr.locClosed e1)).append (Expr.locClosed e2)
theorem Expr.locClosedList : forall (es : List Expr), LocClosed (Expr.localsList es)
  | [] => fun _ h => by cases h
  | e :: es => by simp only [Expr.localsList]; exact (Expr.locClosed e).append (Expr.locClosedList es)
theorem Method.locClosed : forall (M : Method), LocClosed M.locals
  | .mk _ _ _ _ e => by simp only [Method.locals]; exact Expr.locClosed e
theorem Method.locClosedList : forall (Ms : List Method), LocClosed (Method.localsList Ms)
  | [] => fun _ h => by cases h
  | M :: Ms => by simp only [Method.localsList]; exact (Method.locClosed M).append (Method.locClosedList Ms)
end

theorem classes_locClosed (d : Decls) : LocClosed (classes d) := by
  intro k hk x hx
  simp only [classes, listMem_iff, List.mem_flatMap] at hk |-
  rcases hk with ⟨D, hD⟩
  refine Exists.intro D (And.intro hD.1 ?_)
  cases hD.2 with
  | head => exact List.Mem.tail _ hx
  | tail _ hk => exact List.Mem.tail _ (Method.locClosedList D.Ms k hk x hx)

theorem ExprCtx.locals_plug {a : Expr} {k : K} (hk : List.Mem k a.locals) :
    forall (E : ExprCtx), List.Mem k (E.plug a).locals := by
  intro E
  induction E <;> simp only [ExprCtx.plug, Expr.locals]
  case hole => exact hk
  all_goals
    rename_i ih
    first | exact List.mem_append_left _ ih | exact ih | exact mem_localsList mem_mid ih
          | exact List.mem_append_right _ (mem_localsList mem_mid ih) | exact List.mem_append_right _ ih
          | exact List.Mem.tail _ (List.mem_append_left _ (mem_localsList mem_mid ih))
          | exact List.mem_append_left _ (List.mem_append_left _ ih)
          | exact List.mem_append_left _ (List.mem_append_right _ ih)

theorem OccursIn.locals {C Fs C' Ts es Ms} {e : Expr} (h : OccursIn (.newLocal C Fs C' Ts es Ms) e) :
    List.Mem (K.loc C Fs C' Ts es Ms) e.locals := by
  rcases h with ⟨E, hE⟩; rw [hE]; exact ExprCtx.locals_plug (List.Mem.head _) E

theorem Declared.mem {d : Decls} {k : K} (h : Declared d k) : List.Mem k (classes d) := by
  induction h with
  | dec h => exact classes_mem_dec h
  | @loc k Delta T0 m ps e C0 Fs C' Ts es Ms hk hM hO ih =>
    exact classes_locClosed d k ih _ (mem_localsListM hM hO.locals)

theorem Declared.unique {d : Decls} (hwf : WFDecls d) {k1 k2 : K} (h1 : Declared d k1) (h2 : Declared d k2)
    (he : k1.name = k2.name) : k1 = k2 :=
  nodup_map_inj hwf.1 h1.mem h2.mem he

theorem Declared.dec_loc {d : Decls} (hwf : WFDecls d) {D : Dec} {C Fs C' Ts es Ms}
    (h1 : Declared d (.dec D)) (h2 : Declared d (.loc C Fs C' Ts es Ms)) (he : D.C = C) : False := by
  have := Declared.unique hwf h1 h2 he
  cases this

theorem MethodIn.dec {d : Decls} (hwf : WFDecls d) {M : Method} {D : Dec} (hD : Declared d (.dec D))
    (h : MethodIn d M D.C) : List.Mem M D.Ms := by
  rcases h with ⟨k, hk⟩
  have := Declared.unique hwf hk.1 hD hk.2.1
  subst this
  exact hk.2.2

theorem MethodIn.loc {d : Decls} (hwf : WFDecls d) {M : Method} {C Fs C' Ts es Ms}
    (hD : Declared d (.loc C Fs C' Ts es Ms)) (h : MethodIn d M C) : List.Mem M Ms := by
  rcases h with ⟨k, hk⟩
  have := Declared.unique hwf hk.1 hD hk.2.1
  subst this
  exact hk.2.2

theorem names_unique {Ms : List Method} {M1 M2 : Method} (hn : (Ms.map Method.name).Nodup) (h1 : List.Mem M1 Ms)
    (h2 : List.Mem M2 Ms) (he : M1.name = M2.name) : M1 = M2 :=
  nodup_map_inj hn h1 h2 he

theorem Declared.namesNodup {d : Decls} (hwf : WFDecls d) {k : K} (h : Declared d k) : (k.Ms.map Method.name).Nodup :=
  hwf.2.2.1 k h.mem

end Funnelling.High
