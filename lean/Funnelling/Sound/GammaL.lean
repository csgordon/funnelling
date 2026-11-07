import Funnelling.Sound.CastRun

open Funnelling.SoundSimp

namespace Funnelling.High

abbrev gdom (gamma : Gamma) : List VarName := gamma.map VarDecl.x

theorem lookup_mem_g {x : VarName} {U : Ty} : forall {gamma : Gamma}, gamma.lookup x = some U ->
    List.Mem { T := U, x := x } gamma
  | [], h => by simp [Gamma.lookup] at h
  | d :: gamma, h => by
    simp only [Gamma.lookup, List.find?_cons] at h
    by_cases e : d.x = x
    . have hb : (d.x == x) = true := by simp [e]
      simp only [hb, Option.map_some] at h
      cases h
      have : d = { T := d.T, x := x } := by cases d; simp_all
      rw [this]; exact List.Mem.head _
    . have hb : (d.x == x) = false := by simp [e]
      simp only [hb] at h
      exact List.Mem.tail _ (lookup_mem_g h)

theorem lookup_of_mem_g {x : VarName} {U : Ty} : forall {gamma : Gamma}, (gdom gamma).Nodup ->
    List.Mem { T := U, x := x } gamma -> gamma.lookup x = some U
  | [], _, h => by cases h
  | d :: gamma, hn, h => by
    simp only [gdom, List.map_cons, List.nodup_cons] at hn
    simp only [Gamma.lookup, List.find?_cons]
    cases h with
    | head => simp
    | tail _ h =>
      have e : Not (d.x = x) := by
        intro e
        apply hn.1
        rw [e]
        exact List.mem_map_of_mem (f := VarDecl.x) h
      have hb : (d.x == x) = false := by simp [e]
      simp only [hb]
      exact lookup_of_mem_g hn.2 h

theorem gdom_filter_nodup {p : VarDecl -> Bool} {gamma : Gamma} (h : (gdom gamma).Nodup) :
    (gdom (gamma.filter p)).Nodup := by
  simp only [gdom]
  exact List.Nodup.sublist (List.Sublist.map _ (List.filter_sublist)) h


mutual
theorem Expr.noShadow_binders : forall {e : Expr} {Xs : List TVarName} {xs : List VarName},
    e.noShadow Xs xs = true -> NoThis e -> forall y, List.Mem y e.vbinders -> Not (List.Mem y xs)
  | .var _, _, _, _, _, y, hy => by cases hy
  | .call e _ _ es, _, _, hn, ht, y, hy => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht hy
    rcases hy with hy | hy
    . exact Expr.noShadow_binders hn.1 ht.1 y hy
    . exact Expr.noShadowList_binders hn.2 ht.2 y hy
  | .superCall e _ _ _ es, _, _, hn, ht, y, hy => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht hy
    rcases hy with hy | hy
    . exact Expr.noShadow_binders hn.1 ht.1 y hy
    . exact Expr.noShadowList_binders hn.2 ht.2 y hy
  | .field e _, _, _, hn, ht, y, hy => by
    simp only [Expr.noShadow] at hn
    simp only [NoThis, Expr.vbinders] at ht hy
    exact Expr.noShadow_binders hn ht y hy
  | .new _ _ es, _, _, hn, ht, y, hy => by
    simp only [Expr.noShadow] at hn
    simp only [NoThis, Expr.vbinders] at ht hy
    exact Expr.noShadowList_binders hn ht y hy
  | .newLocal _ _ _ _ es Ms, _, xs, hn, ht, y, hy => by
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht hy
    rcases hy with hy | hy
    . exact Expr.noShadowList_binders hn.1 ht.1 y hy
    . have h1 := Method.noShadowList_binders hn.2 ht.2 y hy
      intro hm
      apply h1
      have hyt : Not (y = this) := fun e => ht.2 (e ▸ hy)
      simp only [listMem_iff, List.mem_filter]
      exact And.intro hm (by simpa using hyt)
  | .ifInst e0 _ x e1 e2, _, xs, hn, ht, y, hy => by
    simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht hy
    rcases hy with ((hy | hy) | hy) | hy
    . subst hy
      have := hn.1.1.2
      simp at this
      exact this
    . exact Expr.noShadow_binders hn.1.1.1 ht.1.1.2 y hy
    . intro hm
      exact Expr.noShadow_binders hn.1.2 ht.1.2 y hy (List.Mem.tail _ hm)
    . exact Expr.noShadow_binders hn.2 ht.2 y hy
theorem Expr.noShadowList_binders : forall {es : List Expr} {Xs : List TVarName} {xs : List VarName},
    Expr.noShadowList Xs xs es = true -> Not (List.Mem this (Expr.vbindersList es)) ->
    forall y, List.Mem y (Expr.vbindersList es) -> Not (List.Mem y xs)
  | [], _, _, _, _, y, hy => by cases hy
  | e :: es, _, _, hn, ht, y, hy => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at hn
    simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ht hy
    rcases hy with hy | hy
    . exact Expr.noShadow_binders hn.1 ht.1 y hy
    . exact Expr.noShadowList_binders hn.2 ht.2 y hy
theorem Method.noShadow_binders : forall {M : Method} {Xs : List TVarName} {xs : List VarName},
    M.noShadow Xs xs = true -> NoThisM M -> forall y, List.Mem y M.vbinders -> Not (List.Mem y xs)
  | .mk Delta T0 m ps e, _, xs, hn, ht, y, hy => by
    simp only [Method.noShadow, Bool.and_eq_true] at hn
    simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ht hy
    rcases hy with hy | hy
    . exact not_mem_of_all_not_contains hn.1.2 hy
    . intro hm
      exact Expr.noShadow_binders hn.2 ht.2 y hy (List.mem_append_left _ (List.Mem.tail _ hm))
theorem Method.noShadowList_binders : forall {Ms : List Method} {Xs : List TVarName} {xs : List VarName},
    Method.noShadowList Xs xs Ms = true -> Not (List.Mem this (Method.vbindersList Ms)) ->
    forall y, List.Mem y (Method.vbindersList Ms) -> Not (List.Mem y xs)
  | [], _, _, _, _, y, hy => by cases hy
  | M :: Ms, _, _, hn, ht, y, hy => by
    simp only [Method.noShadowList, Bool.and_eq_true] at hn
    simp only [Method.vbindersList, listMem_iff, List.mem_append, not_or] at ht hy
    rcases hy with hy | hy
    . exact Method.noShadow_binders hn.1 ht.1 y hy
    . exact Method.noShadowList_binders hn.2 ht.2 y hy
end

theorem noShadowList_append {Xs : List TVarName} {xs : List VarName} {es1 es2 : List Expr} :
    Expr.noShadowList Xs xs (es1 ++ es2) = (Expr.noShadowList Xs xs es1 && Expr.noShadowList Xs xs es2) := by
  induction es1 with
  | nil => simp [Expr.noShadowList]
  | cons e es ih => simp [Expr.noShadowList, ih, Bool.and_assoc]

theorem vbindersList_append {es1 es2 : List Expr} :
    Expr.vbindersList (es1 ++ es2) = Expr.vbindersList es1 ++ Expr.vbindersList es2 := by
  induction es1 with
  | nil => simp [Expr.vbindersList]
  | cons e es ih => simp [Expr.vbindersList, ih]

theorem uniqList_append {es1 es2 : List Expr} :
    Expr.uniqList (es1 ++ es2) <-> Expr.uniqList es1 /\ Expr.uniqList es2 := by
  induction es1 with
  | nil => simp [Expr.uniqList]
  | cons e es ih => simp [Expr.uniqList, ih, and_assoc]

end Funnelling.High