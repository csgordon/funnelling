import Funnelling.Sound.BaseStep

open Funnelling.SoundSimp

namespace Funnelling.High

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
    . refine Or.inr ?_
      have := List.mem_map.mp hx
      cases this with
      | intro p hp => rw [<- hp.2]; exact List.mem_map_of_mem (List.mem_filter.mp hp.1).1
  | .ifInst e0 T0 x e1 e2, n, T, S, hc => by
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true] at hc |-
    exact And.intro (And.intro (And.intro (Expr.closed_of_vsubst hc.1.1.1) hc.1.1.2)
      (Expr.closed_mono (Expr.closed_of_vsubst hc.1.2) (fun _ h => h) (fun y hy => by
        simp only [listMem_iff, List.mem_append, List.mem_cons] at hy |-
        rcases hy with hy | hy
        . rcases hy with hy | hy
          . exact Or.inl hy
          . exact Or.inr (Or.inl hy)
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
  | .cls C Us, h => by
    simp only [Ty.subst, Ty.ftv] at h |-
    exact Ty.ftvList_of_subst h
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
    have h2 : (Ty.ftvList (Ty.substList s.ty (T0 :: Ts))).all T.contains = true := by
      simpa [Ty.substList] using hc.1.2
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

end Funnelling.High