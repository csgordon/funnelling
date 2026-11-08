import Funnelling.Sound.WFPlug

open Funnelling.SoundSimp

namespace Funnelling.High

abbrev MOk (M : Method) : Prop :=
  (dom M.bounds).Nodup /\ (M.params.map VarDecl.x).Nodup /\ Not (List.Mem this (M.params.map VarDecl.x))

abbrev LocOk (ks : List K) : Prop := forall k, List.Mem k ks -> forall M, List.Mem M k.Ms -> MOk M

theorem LocOk.sub {ks ks' : List K} (h : LocOk ks') (hs : forall k, List.Mem k ks -> List.Mem k ks') : LocOk ks :=
  fun k hk => h k (hs k hk)

theorem LocOk.append_left {ks ks' : List K} (h : LocOk (ks ++ ks')) : LocOk ks :=
  h.sub (fun _ hk => List.mem_append_left _ hk)

theorem LocOk.append_right {ks ks' : List K} (h : LocOk (ks ++ ks')) : LocOk ks' :=
  h.sub (fun _ hk => List.mem_append_right _ hk)

mutual
theorem Expr.uniq_of : forall {e : Expr}, LocOk e.locals -> e.uniq
  | .var _, _ => trivial
  | .call e _ _ es, h => by
    exact And.intro (Expr.uniq_of h.append_left) (Expr.uniqList_of h.append_right)
  | .superCall e _ _ _ es, h => by
    exact And.intro (Expr.uniq_of h.append_left) (Expr.uniqList_of h.append_right)
  | .field e _, h => by
    simp only [Expr.locals] at h; simp only [Expr.uniq]
    exact Expr.uniq_of h
  | .new _ _ es, h => by
    simp only [Expr.locals] at h; simp only [Expr.uniq]
    exact Expr.uniqList_of h
  | .newLocal C Fs C' Ts es Ms, h => by
    simp only [Expr.locals] at h; simp only [Expr.uniq]
    have hk := h _ (List.Mem.head _)
    have h' : LocOk (Expr.localsList es ++ Method.localsList Ms) := h.sub (fun _ hk => List.Mem.tail _ hk)
    exact And.intro (Expr.uniqList_of h'.append_left) (Method.uniqList_of (fun M hM => hk M hM) h'.append_right)
  | .ifInst e0 _ _ e1 e2, h => by
    simp only [Expr.locals] at h; simp only [Expr.uniq]
    exact And.intro (Expr.uniq_of h.append_left.append_left)
      (And.intro (Expr.uniq_of h.append_left.append_right) (Expr.uniq_of h.append_right))
theorem Expr.uniqList_of : forall {es : List Expr}, LocOk (Expr.localsList es) -> Expr.uniqList es
  | [], _ => trivial
  | e :: es, h => by
    simp only [Expr.localsList] at h; simp only [Expr.uniqList]
    exact And.intro (Expr.uniq_of h.append_left) (Expr.uniqList_of h.append_right)
theorem Method.uniq_of : forall {M : Method}, MOk M -> LocOk M.locals -> M.uniq
  | .mk Delta T0 m ps e, h1, h2 => by
    simp only [Method.locals] at h2; simp only [Method.uniq]
    exact And.intro h1.1 (And.intro h1.2.1 (Expr.uniq_of h2))
theorem Method.uniqList_of : forall {Ms : List Method}, (forall M, List.Mem M Ms -> MOk M) ->
    LocOk (Method.localsList Ms) -> Method.uniqList Ms
  | [], _, _ => trivial
  | M :: Ms, h1, h2 => by
    simp only [Method.localsList] at h2; simp only [Method.uniqList]
    exact And.intro (Method.uniq_of (h1 M (List.Mem.head _)) h2.append_left)
      (Method.uniqList_of (fun M' hM' => h1 M' (List.Mem.tail _ hM')) h2.append_right)
end

mutual
theorem Expr.noThis_of : forall {e : Expr}, LocOk e.locals -> Not (List.Mem this e.ifVars) -> NoThis e
  | .var _, _, _ => by simp [NoThis, Expr.vbinders]
  | .call e _ _ es, h, hi => by
    simp only [Expr.locals, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h hi
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or]
    exact And.intro (Expr.noThis_of h.append_left hi.1) (Expr.noThisList_of h.append_right hi.2)
  | .superCall e _ _ _ es, h, hi => by
    simp only [Expr.locals, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h hi
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or]
    exact And.intro (Expr.noThis_of h.append_left hi.1) (Expr.noThisList_of h.append_right hi.2)
  | .field e _, h, hi => by
    simp only [Expr.locals, Expr.ifVars] at h hi
    simp only [NoThis, Expr.vbinders]
    exact Expr.noThis_of h hi
  | .new _ _ es, h, hi => by
    simp only [Expr.locals, Expr.ifVars] at h hi
    simp only [NoThis, Expr.vbinders]
    exact Expr.noThisList_of h hi
  | .newLocal C Fs C' Ts es Ms, h, hi => by
    simp only [Expr.locals, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h hi
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or]
    have hk := h _ (List.Mem.head _)
    have h' : LocOk (Expr.localsList es ++ Method.localsList Ms) := h.sub (fun _ hk => List.Mem.tail _ hk)
    exact And.intro (Expr.noThisList_of h'.append_left hi.1)
      (Method.noThisList_of (fun M hM => hk M hM) h'.append_right hi.2)
  | .ifInst e0 _ x e1 e2, h, hi => by
    simp only [Expr.locals, Expr.ifVars, listMem_iff, List.mem_append, List.mem_cons, not_or] at h hi
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or]
    exact And.intro (And.intro (And.intro hi.1.1.1 (Expr.noThis_of h.append_left.append_left hi.1.1.2))
      (Expr.noThis_of h.append_left.append_right hi.1.2)) (Expr.noThis_of h.append_right hi.2)
theorem Expr.noThisList_of : forall {es : List Expr}, LocOk (Expr.localsList es) ->
    Not (List.Mem this (Expr.ifVarsList es)) -> Not (List.Mem this (Expr.vbindersList es))
  | [], _, _ => by simp [Expr.vbindersList]
  | e :: es, h, hi => by
    simp only [Expr.localsList, Expr.ifVarsList, listMem_iff, List.mem_append, not_or] at h hi
    simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or]
    exact And.intro (Expr.noThis_of h.append_left hi.1) (Expr.noThisList_of h.append_right hi.2)
theorem Method.noThis_of : forall {M : Method}, MOk M -> LocOk M.locals -> Not (List.Mem this M.ifVars) -> NoThisM M
  | .mk Delta T0 m ps e, h1, h2, hi => by
    simp only [Method.locals, Method.ifVars] at h2 hi
    simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or]
    exact And.intro h1.2.2 (Expr.noThis_of h2 hi)
theorem Method.noThisList_of : forall {Ms : List Method}, (forall M, List.Mem M Ms -> MOk M) ->
    LocOk (Method.localsList Ms) -> Not (List.Mem this (Method.ifVarsList Ms)) ->
    Not (List.Mem this (Method.vbindersList Ms))
  | [], _, _, _ => by simp [Method.vbindersList]
  | M :: Ms, h1, h2, hi => by
    simp only [Method.localsList, Method.ifVarsList, listMem_iff, List.mem_append, not_or] at h2 hi
    simp only [Method.vbindersList, listMem_iff, List.mem_append, not_or]
    exact And.intro (Method.noThis_of (h1 M (List.Mem.head _)) h2.append_left hi.1)
      (Method.noThisList_of (fun M' hM' => h1 M' (List.Mem.tail _ hM')) h2.append_right hi.2)
end

theorem WFExpr.locOk {e : Expr} (h : WFExpr e) : LocOk e.locals := by
  intro k hk M hM
  have hm : List.Mem M e.methods := by
    simp only [Expr.methods, listMem_iff, List.mem_flatMap]
    exact Exists.intro k (And.intro hk hM)
  refine And.intro ?_ (And.intro (h.2.1 M hm) (h.2.2.2.2.2.1.1 M hm))
  exact h.2.2.1 M.bounds (by simp only [listMem_iff, List.mem_map]; exact Exists.intro M (And.intro hm rfl))

theorem WFExpr.uniq {e : Expr} (h : WFExpr e) : e.uniq := Expr.uniq_of h.locOk

theorem WFExpr.noThis {e : Expr} (h : WFExpr e) : NoThis e := Expr.noThis_of h.locOk h.2.2.2.2.2.1.2

theorem classes_mem_dec {d : Decls} {D : Dec} (h : List.Mem D d) : List.Mem (K.dec D) (classes d) := by
  simp only [classes, listMem_iff, List.mem_flatMap]
  exact Exists.intro D (And.intro h (List.Mem.head _))

theorem classes_mem_loc {d : Decls} {D : Dec} (h : List.Mem D d) {k : K} (hk : List.Mem k (Method.localsList D.Ms)) :
    List.Mem k (classes d) := by
  simp only [classes, listMem_iff, List.mem_flatMap]
  exact Exists.intro D (And.intro h (List.Mem.tail _ hk))

theorem WFDecls.locOk {d : Decls} (h : WFDecls d) : LocOk (classes d) := by
  intro k hk M hM
  have hm : List.Mem M d.methods := by
    simp only [Decls.methods, listMem_iff, List.mem_flatMap]
    exact Exists.intro k (And.intro hk hM)
  refine And.intro ?_ (And.intro (h.2.2.2.1 M hm) (h.2.2.2.2.2.2.2.1.1 M hm))
  exact h.2.2.2.2.1 M.bounds (by
    simp only [listMem_iff, List.mem_append, List.mem_map]
    exact Or.inr (Exists.intro M (And.intro hm rfl)))

theorem mem_ifVarsListM {M : Method} {x : VarName} : forall {Ms : List Method}, List.Mem M Ms ->
    List.Mem x M.ifVars -> List.Mem x (Method.ifVarsList Ms)
  | _, .head _, hk => by simp only [Method.ifVarsList, listMem_iff, List.mem_append]; exact Or.inl hk
  | _, .tail _ h, hk => by simp only [Method.ifVarsList, listMem_iff, List.mem_append]; exact Or.inr (mem_ifVarsListM h hk)

theorem noShadowListM_mem {M : Method} {Xs : List TVarName} {xs : List VarName} : forall {Ms : List Method},
    List.Mem M Ms -> Method.noShadowList Xs xs Ms = true -> M.noShadow Xs xs = true
  | _, .head _, hn => by simp only [Method.noShadowList, Bool.and_eq_true] at hn; exact hn.1
  | _, .tail _ h, hn => by simp only [Method.noShadowList, Bool.and_eq_true] at hn; exact noShadowListM_mem h hn.2

theorem WFDecls.method {d : Decls} (h : WFDecls d) {D : Dec} (hD : List.Mem D d) {M : Method}
    (hM : List.Mem M D.Ms) : M.uniq /\ NoThisM M /\ Method.noShadow (dom D.bounds) [] M = true := by
  have hl := h.locOk
  have hmo : MOk M := hl (K.dec D) (classes_mem_dec hD) M hM
  have hlm : LocOk M.locals := hl.sub (fun k hk => classes_mem_loc hD (mem_localsListM hM hk))
  have hi : Not (List.Mem this M.ifVars) := by
    intro ht
    apply h.2.2.2.2.2.2.2.1.2
    simp only [listMem_iff, List.mem_flatMap]
    exact Exists.intro D (And.intro hD (mem_ifVarsListM hM ht))
  refine And.intro (Method.uniq_of hmo hlm) (And.intro (Method.noThis_of hmo hlm hi) ?_)
  have h7 := h.2.2.2.2.2.2.1 D hD
  exact noShadowListM_mem hM h7
end Funnelling.High
