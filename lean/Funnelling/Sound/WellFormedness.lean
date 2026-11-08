import Funnelling.Sound.FreshSubstitution

open Funnelling.SoundSimp

namespace Funnelling

abbrev Sub1 {A : Type} (l l' : List A) : Prop := forall x, List.Mem x l -> List.Mem x l'

theorem all_contains_mono {A : Type} [DecidableEq A] {l T T' : List A} (h : l.all T.contains = true)
    (hT : Sub1 T T') : l.all T'.contains = true :=
  all_contains_iff.mpr (fun x hx => hT x (all_contains_iff.mp h x hx))

theorem Sub1.cons {A : Type} {l l' : List A} {a : A} (h : Sub1 l l') : Sub1 (a :: l) (a :: l') := by
  intro x hx
  cases hx with
  | head => exact List.Mem.head _
  | tail _ hx => exact List.Mem.tail _ (h x hx)

theorem Sub1.append {A : Type} {l l' : List A} (m : List A) (h : Sub1 l l') : Sub1 (l ++ m) (l' ++ m) := by
  intro x hx
  simp only [listMem_iff, List.mem_append] at hx |-
  rcases hx with hx | hx
  . exact Or.inl (h x hx)
  . exact Or.inr hx

mutual
theorem Expr.closed_mono : forall {e : Expr} {T T' : List TVarName} {S S' : List VarName},
    e.closed T S = true -> Sub1 T T' -> Sub1 S S' -> e.closed T' S' = true
  | .var x, _, _, S, _, hc, _, hS => by
    simp only [Expr.closed] at hc |-
    have : List.Mem x S := by simpa using hc
    simpa using hS x this
  | .call e Ts m es, _, _, _, _, hc, hT, hS => by
    simp only [Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (Expr.closed_mono hc.1.1 hT hS) (all_contains_mono hc.1.2 hT))
      (Expr.closedList_mono hc.2 hT hS)
  | .superCall e T0 Ts m es, _, _, _, _, hc, hT, hS => by
    simp only [Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (Expr.closed_mono hc.1.1 hT hS) (all_contains_mono hc.1.2 hT))
      (Expr.closedList_mono hc.2 hT hS)
  | .field e f, _, _, _, _, hc, hT, hS => by
    simp only [Expr.closed] at hc |-
    exact Expr.closed_mono hc hT hS
  | .new C Ts es, _, _, _, _, hc, hT, hS => by
    simp only [Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (all_contains_mono hc.1 hT) (Expr.closedList_mono hc.2 hT hS)
  | .newLocal C Fs C' Ts es Ms, _, _, _, _, hc, hT, hS => by
    simp only [Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (all_contains_mono hc.1.1 hT) (Expr.closedList_mono hc.1.2 hT hS))
      (Method.closedList_mono hc.2 hT hS)
  | .ifInst e0 T0 x e1 e2, _, _, _, _, hc, hT, hS => by
    simp only [Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (And.intro (Expr.closed_mono hc.1.1.1 hT hS) (all_contains_mono hc.1.1.2 hT))
      (Expr.closed_mono hc.1.2 hT hS.cons)) (Expr.closed_mono hc.2 hT hS)
theorem Expr.closedList_mono : forall {es : List Expr} {T T' : List TVarName} {S S' : List VarName},
    Expr.closedList T S es = true -> Sub1 T T' -> Sub1 S S' -> Expr.closedList T' S' es = true
  | [], _, _, _, _, _, _, _ => rfl
  | e :: es, _, _, _, _, hc, hT, hS => by
    simp only [Expr.closedList, Bool.and_eq_true] at hc |-
    exact And.intro (Expr.closed_mono hc.1 hT hS) (Expr.closedList_mono hc.2 hT hS)
theorem Method.closed_mono : forall {M : Method} {T T' : List TVarName} {S S' : List VarName},
    M.closed T S = true -> Sub1 T T' -> Sub1 S S' -> M.closed T' S' = true
  | .mk Delta T0 m ps e, _, _, _, _, hc, hT, hS => by
    simp only [Method.closed, Bool.and_eq_true] at hc |-
    exact And.intro (all_contains_mono hc.1 (hT.append _))
      (Expr.closed_mono hc.2 (hT.append _) ((hS.cons).append _))
theorem Method.closedList_mono : forall {Ms : List Method} {T T' : List TVarName} {S S' : List VarName},
    Method.closedList T S Ms = true -> Sub1 T T' -> Sub1 S S' -> Method.closedList T' S' Ms = true
  | [], _, _, _, _, _, _, _ => rfl
  | M :: Ms, _, _, _, _, hc, hT, hS => by
    simp only [Method.closedList, Bool.and_eq_true] at hc |-
    exact And.intro (Method.closed_mono hc.1 hT hS) (Method.closedList_mono hc.2 hT hS)
end

theorem Value.closed_any {v : Value} (h : v.expr.closed [] [] = true) (T : List TVarName) (S : List VarName) :
    v.expr.closed T S = true :=
  Expr.closed_mono h (fun _ hx => by cases hx) (fun _ hx => by cases hx)

theorem lookup_some_mem_dom {A B : Type} [DecidableEq A] {x : A} {y : B} {r : List (Prod A B)}
    (h : List.lookup x r = some y) : List.Mem x (r.map Prod.fst) := by
  have := List.mem_map_of_mem (f := Prod.fst) (lookup_mem h)
  exact this

mutual
theorem Expr.closed_of_vsubst : forall {e : Expr} {n : VSubst} {T : List TVarName} {S : List VarName},
    (e.vsubst n).closed T S = true -> e.closed T (S ++ n.map Prod.fst) = true
  | .var x, n, T, S, hc => by
    simp only [Expr.closed]
    cases hl : List.lookup x n with
    | none =>
      simp only [Expr.vsubst, hl, Expr.closed] at hc
      have : List.Mem x S := by simpa using hc
      simpa using Or.inl this
    | some v =>
      have := lookup_some_mem_dom hl
      simpa using Or.inr this
  | .call e Ts m es, n, T, S, hc => by
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (Expr.closed_of_vsubst hc.1.1) hc.1.2) (Expr.closedList_of_vsubst hc.2)
  | .superCall e T0 Ts m es, n, T, S, hc => by
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (Expr.closed_of_vsubst hc.1.1) hc.1.2) (Expr.closedList_of_vsubst hc.2)
  | .field e f, n, T, S, hc => by
    simp only [Expr.vsubst, Expr.closed] at hc |-
    exact Expr.closed_of_vsubst hc
  | .new C Ts es, n, T, S, hc => by
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro hc.1 (Expr.closedList_of_vsubst hc.2)
  | .newLocal C Fs C' Ts es Ms, n, T, S, hc => by
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true] at hc |-
    refine And.intro (And.intro hc.1.1 (Expr.closedList_of_vsubst hc.1.2)) ?_
    refine Method.closedList_mono (Method.closedList_of_vsubst hc.2) (fun _ h => h) ?_
    intro x hx
    simp only [listMem_iff, List.mem_append] at hx |-
    rcases hx with hx | hx
    . exact Or.inl hx
    . simp_all
  | .ifInst e0 T0 x e1 e2, n, T, S, hc => by
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (And.intro (Expr.closed_of_vsubst hc.1.1.1) hc.1.1.2)
      (Expr.closed_mono (Expr.closed_of_vsubst hc.1.2) (fun _ h => h) (fun y hy => by
        simp only [listMem_iff, List.mem_append, List.mem_cons] at hy |-
        rcases hy with hy | hy
        . grind
        . exact Or.inr (Or.inr hy))))
      (Expr.closed_of_vsubst hc.2)
theorem Expr.closedList_of_vsubst : forall {es : List Expr} {n : VSubst} {T : List TVarName} {S : List VarName},
    Expr.closedList T S (Expr.vsubstList n es) = true -> Expr.closedList T (S ++ n.map Prod.fst) es = true
  | [], _, _, _, _ => rfl
  | e :: es, n, T, S, hc => by
    simp only [Expr.vsubstList, Expr.closedList, Bool.and_eq_true] at hc |-
    exact And.intro (Expr.closed_of_vsubst hc.1) (Expr.closedList_of_vsubst hc.2)
theorem Method.closed_of_vsubst : forall {M : Method} {n : VSubst} {T : List TVarName} {S : List VarName},
    (M.vsubst n).closed T S = true -> M.closed T (S ++ n.map Prod.fst) = true
  | .mk Delta T0 m ps e, n, T, S, hc => by
    simp only [Method.vsubst, Method.closed, Bool.and_eq_true] at hc |-
    refine And.intro hc.1 (Expr.closed_mono (Expr.closed_of_vsubst hc.2) (fun _ h => h) ?_)
    intro y hy
    simp only [listMem_iff, List.mem_append, List.mem_cons] at hy |-
    rcases hy with ((hy | hy) | hy) | hy
    . exact Or.inl (Or.inl hy)
    . exact Or.inl (Or.inr (Or.inl hy))
    . exact Or.inr hy
    . exact Or.inl (Or.inr (Or.inr hy))
theorem Method.closedList_of_vsubst : forall {Ms : List Method} {n : VSubst} {T : List TVarName} {S : List VarName},
    Method.closedList T S (Method.vsubstList n Ms) = true -> Method.closedList T (S ++ n.map Prod.fst) Ms = true
  | [], _, _, _, _ => rfl
  | M :: Ms, n, T, S, hc => by
    simp only [Method.vsubstList, Method.closedList, Bool.and_eq_true] at hc |-
    exact And.intro (Method.closed_of_vsubst hc.1) (Method.closedList_of_vsubst hc.2)
end

mutual
theorem Ty.ftv_of_subst {s : GSubst} {X : TVarName} : forall {U : Ty}, List.Mem X U.ftv ->
    List.Mem X (U.subst s.ty).ftv \/ List.Mem X (s.map Prod.fst)
  | .var Y, h => by
    have e : X = Y := by simpa [Ty.ftv] using h
    subst e
    cases hl : List.lookup X s with
    | none =>
      left
      simp only [Ty.subst, GSubst.lookup_ty, hl, Option.map_none, Option.getD_none, Ty.ftv]
      exact List.Mem.head _
    | some G => exact Or.inr (lookup_some_mem_dom hl)
  | .cls C Us, h => Ty.ftvList_of_subst h
theorem Ty.ftvList_of_subst {s : GSubst} {X : TVarName} : forall {Us : List Ty}, List.Mem X (Ty.ftvList Us) ->
    List.Mem X (Ty.ftvList (Ty.substList s.ty Us)) \/ List.Mem X (s.map Prod.fst)
  | [], h => by cases h
  | U :: Us, h => by
    simp only [Ty.ftvList, Ty.substList, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . rcases Ty.ftv_of_subst h with h' | h'
      . exact Or.inl (Or.inl h')
      . exact Or.inr h'
    . rcases Ty.ftvList_of_subst h with h' | h'
      . exact Or.inl (Or.inr h')
      . exact Or.inr h'
end

theorem all_of_subst {s : GSubst} {T : List TVarName} {Us : List Ty}
    (h : (Ty.ftvList (Ty.substList s.ty Us)).all T.contains = true) :
    (Ty.ftvList Us).all (T ++ s.map Prod.fst).contains = true := by
  apply all_contains_iff.mpr
  intro X hX
  simp only [listMem_iff, List.mem_append]
  rcases Ty.ftvList_of_subst (s := s) hX with h' | h'
  . exact Or.inl (all_contains_iff.mp h X h')
  . exact Or.inr h'

theorem names_subst {s : TSubst} {ps : List VarDecl} : (ps.map (VarDecl.subst s)).map VarDecl.x = ps.map VarDecl.x := by
  simp [List.map_map, Function.comp_def, VarDecl.subst]

theorem substList_eq_map {s : TSubst} : forall {Us : List Ty}, Ty.substList s Us = Us.map (Ty.subst s)
  | [] => rfl
  | U :: Us => by simp [Ty.substList, substList_eq_map]

theorem domF_of_gsubst {s : GSubst} {X : TVarName} : forall {Fs : List Funnel}, List.Mem X (domF Fs) ->
    List.Mem X (domF (Fs.map (Funnel.gsubst s))) \/ List.Mem X (s.map Prod.fst)
  | [], h => by simp [domF] at h
  | F :: Fs, h => by
    rw [domF_cons] at h
    simp only [List.map_cons]
    rw [domF_cons (Fs := List.map (Funnel.gsubst s) Fs)]
    simp only [listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . cases F with
      | ground G => simp [domF] at h
      | funnel Y =>
        have e : X = Y := by simpa [domF] using h
        subst e
        cases hl : List.lookup X s with
        | none => left; left; simp [Funnel.gsubst, hl, domF]
        | some G => exact Or.inr (lookup_some_mem_dom hl)
    . rcases domF_of_gsubst h with h' | h'
      . exact Or.inl (Or.inr h')
      . exact Or.inr h'

mutual
theorem Expr.closed_of_gsubst : forall {e : Expr} {s : GSubst} {T : List TVarName} {S : List VarName},
    (e.gsubst s).closed T S = true -> e.closed (T ++ s.map Prod.fst) S = true
  | .var x, s, T, S, hc => by simpa [Expr.gsubst, Expr.closed] using hc
  | .call e Ts m es, s, T, S, hc => by
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (Expr.closed_of_gsubst hc.1.1) (all_of_subst hc.1.2)) (Expr.closedList_of_gsubst hc.2)
  | .superCall e T0 Ts m es, s, T, S, hc => by
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true] at hc |-
    have h2 : (Ty.ftvList (Ty.substList s.ty (T0 :: Ts))).all T.contains = true := by simpa [Ty.substList] using hc.1.2
    exact And.intro (And.intro (Expr.closed_of_gsubst hc.1.1) (all_of_subst h2)) (Expr.closedList_of_gsubst hc.2)
  | .field e f, s, T, S, hc => by
    simp only [Expr.gsubst, Expr.closed] at hc |-
    exact Expr.closed_of_gsubst hc
  | .new C Ts es, s, T, S, hc => by
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (all_of_subst hc.1) (Expr.closedList_of_gsubst hc.2)
  | .newLocal C Fs C' Ts es Ms, s, T, S, hc => by
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true, List.all_append] at hc |-
    refine And.intro (And.intro (And.intro ?_ (all_of_subst hc.1.1.2)) (Expr.closedList_of_gsubst hc.1.2))
      (Method.closedList_of_gsubst hc.2)
    apply all_contains_iff.mpr
    intro X hX
    simp only [listMem_iff, List.mem_append]
    rcases domF_of_gsubst (s := s) hX with h' | h'
    . exact Or.inl (all_contains_iff.mp hc.1.1.1 X h')
    . exact Or.inr h'
  | .ifInst e0 T0 x e1 e2, s, T, S, hc => by
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true] at hc |-
    have h2 : (Ty.ftvList (Ty.substList s.ty [T0])).all T.contains = true := by
      simpa [Ty.substList, Ty.ftvList] using hc.1.1.2
    have h3 := all_of_subst h2
    simp only [Ty.ftvList, List.append_nil] at h3
    exact And.intro (And.intro (And.intro (Expr.closed_of_gsubst hc.1.1.1) h3) (Expr.closed_of_gsubst hc.1.2))
      (Expr.closed_of_gsubst hc.2)
theorem Expr.closedList_of_gsubst : forall {es : List Expr} {s : GSubst} {T : List TVarName} {S : List VarName},
    Expr.closedList T S (Expr.gsubstList s es) = true -> Expr.closedList (T ++ s.map Prod.fst) S es = true
  | [], _, _, _, _ => rfl
  | e :: es, s, T, S, hc => by
    simp only [Expr.gsubstList, Expr.closedList, Bool.and_eq_true] at hc |-
    exact And.intro (Expr.closed_of_gsubst hc.1) (Expr.closedList_of_gsubst hc.2)
theorem Method.closed_of_gsubst : forall {M : Method} {s : GSubst} {T : List TVarName} {S : List VarName},
    (M.gsubst s).closed T S = true -> M.closed (T ++ s.map Prod.fst) S = true
  | .mk Delta T0 m ps e, s, T, S, hc => by
    simp only [Method.gsubst, Method.closed, Bool.and_eq_true] at hc |-
    rw [dom_bounds_subst] at hc
    have hsub : Sub1 ((T ++ dom Delta) ++ s.map Prod.fst) ((T ++ s.map Prod.fst) ++ dom Delta) := by
      intro X hX
      simp only [listMem_iff, List.mem_append] at hX |-
      rcases hX with (hX | hX) | hX
      . exact Or.inl (Or.inl hX)
      . exact Or.inr hX
      . exact Or.inl (Or.inr hX)
    refine And.intro ?_ (Expr.closed_mono (Expr.closed_of_gsubst hc.2) hsub (fun _ h => by rwa [names_subst] at h))
    have h1 : (Ty.ftvList (Ty.substList s.ty (T0 :: cod Delta ++ ps.map VarDecl.T))).all (T ++ dom Delta).contains = true := by
      have := hc.1
      simp only [substList_eq_map, List.map_cons, List.map_append, cod, Bounds.subst, List.map_map,
        Function.comp_def, VarDecl.subst] at this |-
      exact this
    exact all_contains_mono (all_of_subst h1) hsub
theorem Method.closedList_of_gsubst : forall {Ms : List Method} {s : GSubst} {T : List TVarName} {S : List VarName},
    Method.closedList T S (Method.gsubstList s Ms) = true -> Method.closedList (T ++ s.map Prod.fst) S Ms = true
  | [], _, _, _, _ => rfl
  | M :: Ms, s, T, S, hc => by
    simp only [Method.gsubstList, Method.closedList, Bool.and_eq_true] at hc |-
    exact And.intro (Method.closed_of_gsubst hc.1) (Method.closedList_of_gsubst hc.2)
end

theorem mem_mid {A : Type} {l r : List A} {x : A} : List.Mem x (l ++ x :: r) :=
  List.mem_append_right _ (List.Mem.head _)

theorem ECtx.locals_plug {a : Expr} {k : K} (hk : List.Mem k a.locals) :
    forall (E : ECtx), List.Mem k (E.plug a).locals := by
  intro E
  induction E <;> simp only [ECtx.plug, Expr.locals]
  case hole => exact hk
  all_goals
    rename_i ih
    first | exact List.mem_append_left _ ih | exact ih | exact Expr.mem_localsList mem_mid ih
          | exact List.mem_append_right _ (Expr.mem_localsList mem_mid ih)
          | exact List.Mem.tail _ (List.mem_append_left _ (Expr.mem_localsList mem_mid ih))
          | exact List.mem_append_left _ (List.mem_append_left _ ih)

theorem ECtx.ifVars_plug {a : Expr} {x : VarName} (hk : List.Mem x a.ifVars) :
    forall (E : ECtx), List.Mem x (E.plug a).ifVars := by
  intro E
  induction E <;> simp only [ECtx.plug, Expr.ifVars]
  case hole => exact hk
  all_goals
    rename_i ih
    first | exact List.mem_append_left _ ih | exact ih | exact Expr.mem_ifVarsList mem_mid ih
          | exact List.mem_append_right _ (Expr.mem_ifVarsList mem_mid ih)
          | exact List.mem_append_left _ (Expr.mem_ifVarsList mem_mid ih)
          | exact List.Mem.tail _ (List.mem_append_left _ (List.mem_append_left _ ih))

theorem ECtx.noShadow_plug {a : Expr} {Xs : List TVarName} {xs : List VarName} :
    forall (E : ECtx), (E.plug a).noShadow Xs xs = true -> a.noShadow Xs xs = true := by
  intro E
  induction E <;> intro h <;> simp only [ECtx.plug, Expr.noShadow, Bool.and_eq_true] at h
  case hole => exact h
  all_goals
    rename_i ih
    first | exact ih h | exact ih h.1 | exact ih h.1.1.1 | exact ih (Expr.noShadowList_mem mem_mid h)
          | exact ih (Expr.noShadowList_mem mem_mid h.1) | exact ih (Expr.noShadowList_mem mem_mid h.2)

theorem ECtx.closed_plug {a : Expr} {Xs : List TVarName} {xs : List VarName} :
    forall (E : ECtx), (E.plug a).closed Xs xs = true -> a.closed Xs xs = true := by
  intro E
  induction E <;> intro h <;> simp only [ECtx.plug, Expr.closed, Bool.and_eq_true] at h
  case hole => exact h
  all_goals
    rename_i ih
    first | exact ih h | exact ih h.1.1 | exact ih h.1.1.1 | exact ih (Expr.closedList_mem mem_mid h.2)
          | exact ih (Expr.closedList_mem mem_mid h.1.2)

theorem WFExpr.noShadow {e : Expr} (h : WFExpr e) : e.noShadow [] [] = true := h.2.2.2.2.1

theorem WFExpr.closed {e : Expr} (h : WFExpr e) : e.closed [] [] = true := h.2.2.2.2.2.2

theorem methods_sub {e e' : Expr} (h : forall k, List.Mem k e.locals -> List.Mem k e'.locals) :
    forall M, List.Mem M e.methods -> List.Mem M e'.methods := by
  intro M hM
  simp only [Expr.methods, listMem_iff, List.mem_flatMap] at hM |-
  rcases hM with ⟨k, hk⟩; exact Exists.intro k (And.intro (h k hk.1) hk.2)

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
    (ECtx.noShadow_plug E h.noShadow) (ECtx.closed_plug E h.closed)

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
  | .call e _ _ es, h => And.intro (Expr.uniq_of h.append_left) (Expr.uniqList_of h.append_right)
  | .superCall e _ _ _ es, h => And.intro (Expr.uniq_of h.append_left) (Expr.uniqList_of h.append_right)
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

theorem WFExpr.local_method {C C' : ClassName} {Gs Gs'' : List GTy} {vs0 : List Value} {Ms : List Method} {M : Method}
    (h : WFExpr (Value.newLocal C Gs C' Gs'' vs0 Ms).expr) (hM : List.Mem M Ms) :
    M.noShadow [] [] = true /\ NoThisM M /\ M.uniq /\ M.closed [] [] = true := by
  have hn := h.noShadow
  have ht := WFExpr.noThis h
  have hu := WFExpr.uniq h
  have hc := h.closed
  simp only [Value.expr, Expr.noShadow, Expr.closed, Bool.and_eq_true, NoThis, Expr.vbinders, listMem_iff,
    List.mem_append, not_or, Expr.uniq] at hn ht hu hc
  exact ⟨by simpa using Method.noShadowList_mem hM hn.2, fun h => ht.2 (Method.mem_vbindersList hM h),
    Method.uniqList_mem hM hu.2, Method.closedList_mem hM hc.2⟩

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

theorem WFDecls.method {d : Decls} (h : WFDecls d) {D : Dec} (hD : List.Mem D d) {M : Method}
    (hM : List.Mem M D.Ms) : M.uniq /\ NoThisM M /\ Method.noShadow (dom D.bounds) [] M = true := by
  have hl := h.locOk
  have hmo : MOk M := hl (K.dec D) (classes_mem_dec hD) M hM
  have hlm : LocOk M.locals := hl.sub (fun k hk => classes_mem_loc hD (Method.mem_localsList hM hk))
  have hi : Not (List.Mem this M.ifVars) := by
    intro ht
    apply h.2.2.2.2.2.2.2.1.2
    simp only [listMem_iff, List.mem_flatMap]
    exact Exists.intro D (And.intro hD (Method.mem_ifVarsList hM ht))
  refine And.intro (Method.uniq_of hmo hlm) (And.intro (Method.noThis_of hmo hlm hi) ?_)
  have h7 := h.2.2.2.2.2.2.1 D hD
  exact Method.noShadowList_mem hM h7

end Funnelling
