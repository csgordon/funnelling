import Funnelling.Sound.Closed

open Funnelling.SoundSimp

namespace Funnelling.High

theorem mem_localsList {e : Expr} {k : K} : forall {es : List Expr}, List.Mem e es -> List.Mem k e.locals ->
    List.Mem k (Expr.localsList es)
  | [], h, _ => by cases h
  | e' :: es, h, hk => by
    simp only [Expr.localsList, listMem_iff, List.mem_append]
    cases h with
    | head => exact Or.inl hk
    | tail _ h => exact Or.inr (mem_localsList h hk)

theorem mem_localsListM {M : Method} {k : K} : forall {Ms : List Method}, List.Mem M Ms -> List.Mem k M.locals ->
    List.Mem k (Method.localsList Ms)
  | [], h, _ => by cases h
  | M' :: Ms, h, hk => by
    simp only [Method.localsList, listMem_iff, List.mem_append]
    cases h with
    | head => exact Or.inl hk
    | tail _ h => exact Or.inr (mem_localsListM h hk)

theorem mem_ifVarsList {e : Expr} {x : VarName} : forall {es : List Expr}, List.Mem e es -> List.Mem x e.ifVars ->
    List.Mem x (Expr.ifVarsList es)
  | [], h, _ => by cases h
  | e' :: es, h, hk => by
    simp only [Expr.ifVarsList, listMem_iff, List.mem_append]
    cases h with
    | head => exact Or.inl hk
    | tail _ h => exact Or.inr (mem_ifVarsList h hk)

theorem noShadowList_mem {e : Expr} {Xs : List TVarName} {xs : List VarName} : forall {es : List Expr},
    List.Mem e es -> Expr.noShadowList Xs xs es = true -> e.noShadow Xs xs = true
  | [], h, _ => by cases h
  | e' :: es, h, hn => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at hn
    cases h with
    | head => exact hn.1
    | tail _ h => exact noShadowList_mem h hn.2

theorem closedList_mem {e : Expr} {Xs : List TVarName} {xs : List VarName} : forall {es : List Expr},
    List.Mem e es -> Expr.closedList Xs xs es = true -> e.closed Xs xs = true
  | [], h, _ => by cases h
  | e' :: es, h, hn => by
    simp only [Expr.closedList, Bool.and_eq_true] at hn
    cases h with
    | head => exact hn.1
    | tail _ h => exact closedList_mem h hn.2

theorem mem_mid {A : Type} {l r : List A} {x : A} : List.Mem x (l ++ x :: r) :=
  List.mem_append_right _ (List.Mem.head _)

theorem ECtx.locals_plug {a : Expr} {k : K} (hk : List.Mem k a.locals) :
    forall (E : ECtx), List.Mem k (E.plug a).locals := by
  intro E
  induction E <;> simp only [ECtx.plug, Expr.locals]
  case hole => exact hk
  all_goals
    rename_i ih
    first | exact List.mem_append_left _ ih | exact ih | exact mem_localsList mem_mid ih
          | exact List.mem_append_right _ (mem_localsList mem_mid ih)
          | exact List.Mem.tail _ (List.mem_append_left _ (mem_localsList mem_mid ih))
          | exact List.mem_append_left _ (List.mem_append_left _ ih)

theorem ECtx.ifVars_plug {a : Expr} {x : VarName} (hk : List.Mem x a.ifVars) :
    forall (E : ECtx), List.Mem x (E.plug a).ifVars := by
  intro E
  induction E <;> simp only [ECtx.plug, Expr.ifVars]
  case hole => exact hk
  all_goals
    rename_i ih
    first | exact List.mem_append_left _ ih | exact ih | exact mem_ifVarsList mem_mid ih
          | exact List.mem_append_right _ (mem_ifVarsList mem_mid ih)
          | exact List.mem_append_left _ (mem_ifVarsList mem_mid ih)
          | exact List.Mem.tail _ (List.mem_append_left _ (List.mem_append_left _ ih))

theorem ECtx.noShadow_plug {a : Expr} {Xs : List TVarName} {xs : List VarName} :
    forall (E : ECtx), (E.plug a).noShadow Xs xs = true -> a.noShadow Xs xs = true := by
  intro E
  induction E <;> intro h <;> simp only [ECtx.plug, Expr.noShadow, Bool.and_eq_true] at h
  case hole => exact h
  all_goals
    rename_i ih
    first | exact ih h | exact ih h.1 | exact ih h.1.1.1 | exact ih (noShadowList_mem mem_mid h)
          | exact ih (noShadowList_mem mem_mid h.1) | exact ih (noShadowList_mem mem_mid h.2)

theorem ECtx.closed_plug {a : Expr} {Xs : List TVarName} {xs : List VarName} :
    forall (E : ECtx), (E.plug a).closed Xs xs = true -> a.closed Xs xs = true := by
  intro E
  induction E <;> intro h <;> simp only [ECtx.plug, Expr.closed, Bool.and_eq_true] at h
  case hole => exact h
  all_goals
    rename_i ih
    first | exact ih h | exact ih h.1.1 | exact ih h.1.1.1 | exact ih (closedList_mem mem_mid h.2)
          | exact ih (closedList_mem mem_mid h.1.2)

theorem methods_sub {e e' : Expr} (h : forall k, List.Mem k e.locals -> List.Mem k e'.locals) :
    forall M, List.Mem M e.methods -> List.Mem M e'.methods := by
  intro M hM
  simp only [Expr.methods, listMem_iff, List.mem_flatMap] at hM |-
  cases hM with
  | intro k hk => exact Exists.intro k (And.intro (h k hk.1) hk.2)

theorem WFExpr.sub {e e' : Expr} (h : WFExpr e') (hl : forall k, List.Mem k e.locals -> List.Mem k e'.locals)
    (hi : forall x, List.Mem x e.ifVars -> List.Mem x e'.ifVars) (hn : e.noShadow [] [] = true)
    (hc : e.closed [] [] = true) : WFExpr e := by
  have hm := methods_sub hl
  refine And.intro (fun k hk => h.1 k (hl k hk)) (And.intro (fun M hM => h.2.1 M (hm M hM))
    (And.intro ?_ (And.intro (fun k hk => h.2.2.2.1 k (hl k hk)) (And.intro hn (And.intro ?_ hc)))))
  . intro D hD
    simp only [listMem_iff, List.mem_map] at hD
    cases hD with
    | intro M hM => exact h.2.2.1 D (by simp only [listMem_iff, List.mem_map]; exact Exists.intro M (And.intro (hm M hM.1) hM.2))
  . exact And.intro (fun M hM => h.2.2.2.2.2.1.1 M (hm M hM)) (fun ht => h.2.2.2.2.2.1.2 (hi this ht))

theorem WFExpr.plug {E : ECtx} {a : Expr} (h : WFExpr (E.plug a)) : WFExpr a :=
  WFExpr.sub h (fun _ hk => ECtx.locals_plug hk E) (fun _ hx => ECtx.ifVars_plug hx E)
    (ECtx.noShadow_plug E h.2.2.2.2.1) (ECtx.closed_plug E h.2.2.2.2.2.2)

theorem RenEs.mid {a b : Expr} (h : RenE [] [] a b) : forall (l r : List Expr), RenEs [] [] (l ++ a :: r) (l ++ b :: r)
  | [], r => RenEs.cons h (RenEs.refl (by intro p hp; cases hp) (by intro p hp; cases hp) r)
  | e :: l, r => RenEs.cons (RenE.refl (by intro p hp; cases hp) (by intro p hp; cases hp) e) (RenEs.mid h l r)

theorem RenE.plug {a b : Expr} (h : RenE [] [] a b) : forall (E : ECtx), RenE [] [] (E.plug a) (E.plug b)
  | .hole => h
  | .callRecv E Gs m es => by
    have := RenE.call (m := m) (Ts := GTy.tys Gs) (RenE.plug h E) (RenEs.refl (by intro p hp; cases hp) (by intro p hp; cases hp) es)
    rwa [Ty.renList_idRen (by intro p hp; cases hp)] at this
  | .callArg v Gs m vs E es => by
    have := RenE.call (m := m) (Ts := GTy.tys Gs) (RenE.refl (by intro p hp; cases hp) (by intro p hp; cases hp) v.expr)
      (RenEs.mid (RenE.plug h E) (Value.exprs vs) es)
    rwa [Ty.renList_idRen (by intro p hp; cases hp)] at this
  | .superRecv E G Gs m es => by
    have := RenE.superCall (m := m) (T := G.ty) (Ts := GTy.tys Gs) (RenE.plug h E)
      (RenEs.refl (by intro p hp; cases hp) (by intro p hp; cases hp) es)
    rwa [Ty.renList_idRen (by intro p hp; cases hp), Ty.ren_idRen (by intro p hp; cases hp)] at this
  | .superArg v G Gs m vs E es => by
    have := RenE.superCall (m := m) (T := G.ty) (Ts := GTy.tys Gs)
      (RenE.refl (by intro p hp; cases hp) (by intro p hp; cases hp) v.expr) (RenEs.mid (RenE.plug h E) (Value.exprs vs) es)
    rwa [Ty.renList_idRen (by intro p hp; cases hp), Ty.ren_idRen (by intro p hp; cases hp)] at this
  | .field E f => RenE.field (RenE.plug h E)
  | .newArg C Gs vs E es => by
    have := RenE.new (C := C) (Ts := GTy.tys Gs) (RenEs.mid (RenE.plug h E) (Value.exprs vs) es)
    rwa [Ty.renList_idRen (by intro p hp; cases hp)] at this
  | .localArg C Gs C' Gs' vs E es Ms => by
    have := RenE.newLocal (C := C) (Fs := Gs.map Funnel.ground) (C' := C') (Ts := GTy.tys Gs')
      (RenEs.mid (RenE.plug h E) (Value.exprs vs) es) (RenMs.refl (by intro p hp; cases hp) (by intro p hp; cases hp) Ms)
    rwa [Ty.renList_idRen (by intro p hp; cases hp), Funnels.ren_id (fun X _ => rn_id (by intro p hp; cases hp) X)] at this
  | .ifCond E G x e1 e2 => by
    have := RenE.ifInst (T := G.ty) (y := x) (RenE.plug h E)
      (RenE.refl (IdRen.cons (by intro p hp; cases hp)) (by intro p hp; cases hp) e1)
      (RenE.refl (by intro p hp; cases hp) (by intro p hp; cases hp) e2)
    rwa [Ty.ren_idRen (by intro p hp; cases hp)] at this

theorem Fresh.plug {a b : Expr} (h : Fresh a b) (E : ECtx) : Fresh (E.plug a) (E.plug b) :=
  And.intro (RenE.plug h.1 E) (RenE.plug h.2 E)

end Funnelling.High
