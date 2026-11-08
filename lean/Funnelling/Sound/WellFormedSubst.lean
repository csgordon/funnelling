import Funnelling.Sound.Progress

open Funnelling.SoundSimp

namespace Funnelling

def KNodup (Ms : List Method) (Fs : List Funnel) : Prop := (Ms.map Method.name).Nodup /\ (domF Fs).Nodup /\
  forall M, List.Mem M Ms -> (M.params.map VarDecl.x).Nodup /\ (dom M.bounds).Nodup /\
    Not (List.Mem this (M.params.map VarDecl.x))

abbrev K.Nodup (k : K) : Prop := KNodup k.Ms k.Fs

theorem KNodup.vsubst {n : VSubst} {Ms : List Method} {Fs : List Funnel} (h : KNodup Ms Fs) :
    KNodup (Method.vsubstList n Ms) Fs := by
  unfold KNodup at h |-
  refine ⟨by rw [names_vsubst]; exact h.1, h.2.1, fun M hM => ?_⟩
  rcases Method.vsubstList_mem hM with ⟨M0, hM0, e⟩
  subst e
  cases M0 with
  | mk D T m ps b => exact h.2.2 (Method.mk D T m ps b) hM0

abbrev VLoc (n : VSubst) : Prop := forall p, List.Mem p n -> forall k, List.Mem k p.2.expr.locals -> K.Nodup k

mutual
theorem Expr.nodup_vsubst : forall {e : Expr} {n : VSubst}, (forall k, List.Mem k e.locals -> K.Nodup k) -> VLoc n ->
    forall k, List.Mem k (e.vsubst n).locals -> K.Nodup k
  | .var x, n, _, hn => by
    intro k hk
    cases hl : List.lookup x n with
    | none => simp [Expr.vsubst, hl, Expr.locals] at hk
    | some v => simp only [Expr.vsubst, hl] at hk; exact hn (x, v) (lookup_mem hl) k hk
  | .call _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨Expr.nodup_vsubst h.1 hn, Expr.nodup_vsubstList h.2 hn⟩
  | .superCall _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨Expr.nodup_vsubst h.1 hn, Expr.nodup_vsubstList h.2 hn⟩
  | .field _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals] at h |-
    exact Expr.nodup_vsubst h hn
  | .new _ _ _, _, h, hn => Expr.nodup_vsubstList h hn
  | .newLocal _ _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals, listMem_iff, List.mem_append, List.mem_cons, or_imp, forall_and,
      forall_eq] at h |-
    exact ⟨KNodup.vsubst h.1, Expr.nodup_vsubstList h.2.1 hn,
      Method.nodup_vsubstList h.2.2 (fun p hp => hn p (List.mem_filter.mp hp).1)⟩
  | .ifInst _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨⟨Expr.nodup_vsubst h.1.1 hn, Expr.nodup_vsubst h.1.2 hn⟩, Expr.nodup_vsubst h.2 hn⟩
theorem Expr.nodup_vsubstList : forall {es : List Expr} {n : VSubst},
    (forall k, List.Mem k (Expr.localsList es) -> K.Nodup k) -> VLoc n ->
    forall k, List.Mem k (Expr.localsList (Expr.vsubstList n es)) -> K.Nodup k
  | [], _, _, _ => by intro k hk; simp [Expr.vsubstList, Expr.localsList] at hk
  | _ :: _, _, h, hn => by
    simp only [Expr.vsubstList, Expr.localsList, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨Expr.nodup_vsubst h.1 hn, Expr.nodup_vsubstList h.2 hn⟩
theorem Method.nodup_vsubst : forall {M : Method} {n : VSubst}, (forall k, List.Mem k M.locals -> K.Nodup k) -> VLoc n ->
    forall k, List.Mem k (M.vsubst n).locals -> K.Nodup k
  | .mk _ _ _ _ _, _, h, hn => Expr.nodup_vsubst h hn
theorem Method.nodup_vsubstList : forall {Ms : List Method} {n : VSubst},
    (forall k, List.Mem k (Method.localsList Ms) -> K.Nodup k) -> VLoc n ->
    forall k, List.Mem k (Method.localsList (Method.vsubstList n Ms)) -> K.Nodup k
  | [], _, _, _ => by intro k hk; simp [Method.vsubstList, Method.localsList] at hk
  | _ :: _, _, h, hn => by
    simp only [Method.vsubstList, Method.localsList, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨Method.nodup_vsubst h.1 hn, Method.nodup_vsubstList h.2 hn⟩
end

mutual
theorem Expr.ifVars_vsubst {z : VarName} : forall {e : Expr} {n : VSubst}, Not (List.Mem z e.ifVars) ->
    (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.ifVars)) -> Not (List.Mem z (e.vsubst n).ifVars)
  | .var x, n, _, hn => by
    cases hl : List.lookup x n with
    | none => simp [Expr.vsubst, hl, Expr.ifVars]
    | some v => simp only [Expr.vsubst, hl]; exact hn (x, v) (lookup_mem hl)
  | .call _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h |-
    exact ⟨Expr.ifVars_vsubst h.1 hn, Expr.ifVarsList_vsubst h.2 hn⟩
  | .superCall _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h |-
    exact ⟨Expr.ifVars_vsubst h.1 hn, Expr.ifVarsList_vsubst h.2 hn⟩
  | .field _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars] at h |-
    exact Expr.ifVars_vsubst h hn
  | .new _ _ _, _, h, hn => Expr.ifVarsList_vsubst h hn
  | .newLocal _ _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h |-
    exact ⟨Expr.ifVarsList_vsubst h.1 hn, Method.ifVarsList_vsubst h.2 (fun p hp => hn p (List.mem_filter.mp hp).1)⟩
  | .ifInst _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars, listMem_iff, List.mem_append, List.mem_cons, not_or] at h |-
    exact ⟨⟨⟨h.1.1.1, Expr.ifVars_vsubst h.1.1.2 hn⟩, Expr.ifVars_vsubst h.1.2 hn⟩, Expr.ifVars_vsubst h.2 hn⟩
theorem Expr.ifVarsList_vsubst {z : VarName} : forall {es : List Expr} {n : VSubst},
    Not (List.Mem z (Expr.ifVarsList es)) -> (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.ifVars)) ->
    Not (List.Mem z (Expr.ifVarsList (Expr.vsubstList n es)))
  | [], _, _, _ => by simp [Expr.vsubstList, Expr.ifVarsList]
  | _ :: _, _, h, hn => by
    simp only [Expr.vsubstList, Expr.ifVarsList, listMem_iff, List.mem_append, not_or] at h |-
    exact ⟨Expr.ifVars_vsubst h.1 hn, Expr.ifVarsList_vsubst h.2 hn⟩
theorem Method.ifVars_vsubst {z : VarName} : forall {M : Method} {n : VSubst}, Not (List.Mem z M.ifVars) ->
    (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.ifVars)) -> Not (List.Mem z (M.vsubst n).ifVars)
  | .mk _ _ _ _ _, _, h, hn => Expr.ifVars_vsubst h hn
theorem Method.ifVarsList_vsubst {z : VarName} : forall {Ms : List Method} {n : VSubst},
    Not (List.Mem z (Method.ifVarsList Ms)) -> (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.ifVars)) ->
    Not (List.Mem z (Method.ifVarsList (Method.vsubstList n Ms)))
  | [], _, _, _ => by simp [Method.vsubstList, Method.ifVarsList]
  | _ :: _, _, h, hn => by
    simp only [Method.vsubstList, Method.ifVarsList, listMem_iff, List.mem_append, not_or] at h |-
    exact ⟨Method.ifVars_vsubst h.1 hn, Method.ifVarsList_vsubst h.2 hn⟩
end

mutual
theorem Expr.closed_vsubst : forall {e : Expr} {n : VSubst} {T : List TVarName} {S : List VarName},
    e.closed T (S ++ n.map Prod.fst) = true -> (forall p, List.Mem p n -> p.2.expr.closed [] [] = true) ->
    (e.vsubst n).closed T S = true
  | .var x, n, T, S, hc, hn => by
    cases hl : List.lookup x n with
    | none =>
      simp only [Expr.vsubst, hl, Expr.closed] at hc |-
      have hm : List.Mem x (S ++ n.map Prod.fst) := List.contains_iff_mem.mp hc
      rcases List.mem_append.mp hm with hm | hm
      . exact List.contains_iff_mem.mpr hm
      . exact absurd hm (lookup_none_not_dom hl)
    | some v =>
      simp only [Expr.vsubst, hl]
      exact Value.closed_any (hn (x, v) (lookup_mem hl)) T S
  | .call _ _ _ _, _, _, _, hc, hn => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true]
    exact ⟨⟨Expr.closed_vsubst hc.1.1 hn, hc.1.2⟩, Expr.closedList_vsubst hc.2 hn⟩
  | .superCall _ _ _ _ _, _, _, _, hc, hn => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true]
    exact ⟨⟨Expr.closed_vsubst hc.1.1 hn, hc.1.2⟩, Expr.closedList_vsubst hc.2 hn⟩
  | .field _ _, _, _, _, hc, hn => by
    simp only [Expr.vsubst, Expr.closed]
    exact Expr.closed_vsubst hc hn
  | .new _ _ _, _, _, _, hc, hn => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true]
    exact ⟨hc.1, Expr.closedList_vsubst hc.2 hn⟩
  | .newLocal _ _ _ _ _ _, _, _, _, hc, hn => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true]
    exact ⟨⟨hc.1.1, Expr.closedList_vsubst hc.1.2 hn⟩, Method.closedList_vsubst hc.2 hn⟩
  | .ifInst _ _ x _ _, n, T, S, hc, hn => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vsubst, Expr.closed, Bool.and_eq_true]
    refine ⟨⟨⟨Expr.closed_vsubst hc.1.1.1 hn, hc.1.1.2⟩,
      Expr.closed_vsubst (Expr.closed_mono hc.1.2 (fun _ h => h) ?_) hn⟩, Expr.closed_vsubst hc.2 hn⟩
    intro y hy
    simp only [listMem_iff, List.mem_append, List.mem_cons] at hy |-
    rcases hy with hy | hy | hy
    . exact Or.inl (Or.inl hy)
    . exact Or.inl (Or.inr hy)
    . exact Or.inr hy
theorem Expr.closedList_vsubst : forall {es : List Expr} {n : VSubst} {T : List TVarName} {S : List VarName},
    Expr.closedList T (S ++ n.map Prod.fst) es = true -> (forall p, List.Mem p n -> p.2.expr.closed [] [] = true) ->
    Expr.closedList T S (Expr.vsubstList n es) = true
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _, _, hc, hn => by
    simp only [Expr.closedList, Bool.and_eq_true] at hc
    simp only [Expr.vsubstList, Expr.closedList, Bool.and_eq_true]
    exact ⟨Expr.closed_vsubst hc.1 hn, Expr.closedList_vsubst hc.2 hn⟩
theorem Method.closed_vsubst : forall {M : Method} {n : VSubst} {T : List TVarName} {S : List VarName},
    M.closed T (S ++ n.map Prod.fst) = true -> (forall p, List.Mem p n -> p.2.expr.closed [] [] = true) ->
    (M.vsubst (n.filter fun p => p.1 != this)).closed T S = true
  | .mk _ _ _ _ _, n, T, S, hc, hn => by
    simp only [Method.closed, Bool.and_eq_true] at hc
    simp only [Method.vsubst, Method.closed, Bool.and_eq_true]
    refine ⟨hc.1, Expr.closed_vsubst (Expr.closed_mono hc.2 (fun _ h => h) ?_)
      (fun p hp => hn p (List.mem_filter.mp hp).1)⟩
    intro y hy
    simp only [listMem_iff, List.mem_append, List.mem_cons] at hy |-
    rcases hy with (hy | hy | hy) | hy
    . exact Or.inl (Or.inl (Or.inl hy))
    . exact Or.inl (Or.inl (Or.inr hy))
    . by_cases hyt : y = this
      . exact Or.inl (Or.inl (Or.inl hyt))
      . simp_all
    . exact Or.inl (Or.inr hy)
theorem Method.closedList_vsubst : forall {Ms : List Method} {n : VSubst} {T : List TVarName} {S : List VarName},
    Method.closedList T (S ++ n.map Prod.fst) Ms = true -> (forall p, List.Mem p n -> p.2.expr.closed [] [] = true) ->
    Method.closedList T S (Method.vsubstList (n.filter fun p => p.1 != this) Ms) = true
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _, _, hc, hn => by
    simp only [Method.closedList, Bool.and_eq_true] at hc
    simp only [Method.vsubstList, Method.closedList, Bool.and_eq_true]
    exact ⟨Method.closed_vsubst hc.1 hn, Method.closedList_vsubst hc.2 hn⟩
end

theorem domF_gsubst_sub {s : GSubst} : forall (Fs : List Funnel),
    (domF (Fs.map (Funnel.gsubst s))).Sublist (domF Fs) /\
      forall X, List.Mem X (domF (Fs.map (Funnel.gsubst s))) -> Not (List.Mem X (s.map Prod.fst))
  | [] => ⟨by simp [domF], fun X hX => by simp [domF] at hX⟩
  | F :: Fs => by
    have ih := domF_gsubst_sub (s := s) Fs
    rw [List.map_cons, domF_cons, domF_cons (F := F)]
    cases F with
    | ground G =>
      simp only [domF, List.filterMap_cons, List.filterMap_nil, List.nil_append] at ih |-
      exact ih
    | funnel Y =>
      cases hl : List.lookup Y s with
      | none =>
        simp only [Funnel.gsubst, hl, domF, List.filterMap_cons, List.filterMap_nil, List.singleton_append] at ih |-
        refine ⟨List.Sublist.cons_cons _ ih.1, fun X hX => ?_⟩
        cases hX with
        | head => exact fun hm => by cases lookup_isSome hm with | intro v hv => rw [hv] at hl; cases hl
        | tail _ h => exact ih.2 X h
      | some G =>
        simp only [Funnel.gsubst, hl, domF, List.filterMap_cons, List.filterMap_nil, List.nil_append,
          List.singleton_append] at ih |-
        exact ⟨List.Sublist.cons _ ih.1, ih.2⟩

theorem KNodup.gsubst {s : GSubst} {Ms : List Method} {Fs : List Funnel} (h : KNodup Ms Fs) :
    KNodup (Method.gsubstList s Ms) (Fs.map (Funnel.gsubst s)) := by
  unfold KNodup at h |-
  refine ⟨by rw [names_gsubst]; exact h.1, List.Nodup.sublist (domF_gsubst_sub Fs).1 h.2.1, fun M hM => ?_⟩
  rcases Method.gsubstList_mem hM with ⟨M0, hM0, e⟩
  subst e
  cases M0 with
  | mk D T m ps b =>
    have := h.2.2 (Method.mk D T m ps b) hM0
    simp only [Method.gsubst, Method.params, Method.bounds, names_subst, dom_bounds_subst] at this |-
    exact this

mutual
theorem Expr.nodup_gsubst {s : GSubst} : forall {e : Expr}, (forall k, List.Mem k e.locals -> K.Nodup k) ->
    forall k, List.Mem k (e.gsubst s).locals -> K.Nodup k
  | .var _, _ => by intro k hk; simp [Expr.gsubst, Expr.locals] at hk
  | .call _ _ _ _, h => by
    simp only [Expr.gsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨Expr.nodup_gsubst h.1, Expr.nodup_gsubstList h.2⟩
  | .superCall _ _ _ _ _, h => by
    simp only [Expr.gsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨Expr.nodup_gsubst h.1, Expr.nodup_gsubstList h.2⟩
  | .field _ _, h => by
    simp only [Expr.gsubst, Expr.locals] at h |-
    exact Expr.nodup_gsubst h
  | .new _ _ _, h => Expr.nodup_gsubstList h
  | .newLocal _ _ _ _ _ _, h => by
    simp only [Expr.gsubst, Expr.locals, listMem_iff, List.mem_append, List.mem_cons, or_imp, forall_and,
      forall_eq] at h |-
    exact ⟨KNodup.gsubst h.1, Expr.nodup_gsubstList h.2.1, Method.nodup_gsubstList h.2.2⟩
  | .ifInst _ _ _ _ _, h => by
    simp only [Expr.gsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨⟨Expr.nodup_gsubst h.1.1, Expr.nodup_gsubst h.1.2⟩, Expr.nodup_gsubst h.2⟩
theorem Expr.nodup_gsubstList {s : GSubst} : forall {es : List Expr},
    (forall k, List.Mem k (Expr.localsList es) -> K.Nodup k) ->
    forall k, List.Mem k (Expr.localsList (Expr.gsubstList s es)) -> K.Nodup k
  | [], _ => by intro k hk; simp [Expr.gsubstList, Expr.localsList] at hk
  | _ :: _, h => by
    simp only [Expr.gsubstList, Expr.localsList, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨Expr.nodup_gsubst h.1, Expr.nodup_gsubstList h.2⟩
theorem Method.nodup_gsubst {s : GSubst} : forall {M : Method}, (forall k, List.Mem k M.locals -> K.Nodup k) ->
    forall k, List.Mem k (M.gsubst s).locals -> K.Nodup k
  | .mk _ _ _ _ _, h => Expr.nodup_gsubst h
theorem Method.nodup_gsubstList {s : GSubst} : forall {Ms : List Method},
    (forall k, List.Mem k (Method.localsList Ms) -> K.Nodup k) ->
    forall k, List.Mem k (Method.localsList (Method.gsubstList s Ms)) -> K.Nodup k
  | [], _ => by intro k hk; simp [Method.gsubstList, Method.localsList] at hk
  | _ :: _, h => by
    simp only [Method.gsubstList, Method.localsList, listMem_iff, List.mem_append, or_imp, forall_and] at h |-
    exact ⟨Method.nodup_gsubst h.1, Method.nodup_gsubstList h.2⟩
end

theorem Ty.ftvList_subst_all {s : GSubst} {T : List TVarName} {Us : List Ty}
    (h : (Ty.ftvList Us).all (T ++ s.map Prod.fst).contains = true) :
    (Ty.ftvList (Ty.substList s.ty Us)).all T.contains = true := by
  apply all_contains_iff.mpr
  intro X hX
  have h' := Ty.ftvList_gsubst hX
  rcases List.mem_append.mp (all_contains_iff.mp h X h'.1) with hm | hm
  . exact hm
  . exact absurd hm h'.2

theorem Ty.ftv_subst_all {s : GSubst} {T : List TVarName} {U : Ty}
    (h : U.ftv.all (T ++ s.map Prod.fst).contains = true) : (U.subst s.ty).ftv.all T.contains = true := by
  apply all_contains_iff.mpr
  intro X hX
  have h' := Ty.ftv_gsubst hX
  rcases List.mem_append.mp (all_contains_iff.mp h X h'.1) with hm | hm
  . exact hm
  . exact absurd hm h'.2

mutual
theorem Expr.closed_gsubst {s : GSubst} : forall {e : Expr} {T : List TVarName} {S : List VarName},
    e.closed (T ++ s.map Prod.fst) S = true -> (e.gsubst s).closed T S = true
  | .var _, _, _, hc => hc
  | .call _ _ _ _, _, _, hc => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true]
    exact ⟨⟨Expr.closed_gsubst hc.1.1, Ty.ftvList_subst_all hc.1.2⟩, Expr.closedList_gsubst hc.2⟩
  | .superCall _ T0 Ts _ _, _, _, hc => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true]
    exact ⟨⟨Expr.closed_gsubst hc.1.1, Ty.ftvList_subst_all (Us := T0 :: Ts) hc.1.2⟩, Expr.closedList_gsubst hc.2⟩
  | .field _ _, _, _, hc => by
    simp only [Expr.gsubst, Expr.closed]
    exact Expr.closed_gsubst hc
  | .new _ _ _, _, _, hc => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true]
    exact ⟨Ty.ftvList_subst_all hc.1, Expr.closedList_gsubst hc.2⟩
  | .newLocal _ Fs _ Ts _ _, T, _, hc => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true]
    refine ⟨⟨?_, Expr.closedList_gsubst hc.1.2⟩, Method.closedList_gsubst hc.2⟩
    have h1 := hc.1.1
    rw [List.all_append, Bool.and_eq_true] at h1 |-
    refine ⟨?_, Ty.ftvList_subst_all h1.2⟩
    apply all_contains_iff.mpr
    intro X hX
    have hd := domF_gsubst_sub (s := s) Fs
    rcases List.mem_append.mp (all_contains_iff.mp h1.1 X (hd.1.subset hX)) with hm | hm
    . exact hm
    . exact absurd hm (hd.2 X hX)
  | .ifInst _ _ x _ _, T, S, hc => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.gsubst, Expr.closed, Bool.and_eq_true]
    exact ⟨⟨⟨Expr.closed_gsubst hc.1.1.1, Ty.ftv_subst_all hc.1.1.2⟩, Expr.closed_gsubst hc.1.2⟩, Expr.closed_gsubst hc.2⟩
theorem Expr.closedList_gsubst {s : GSubst} : forall {es : List Expr} {T : List TVarName} {S : List VarName},
    Expr.closedList (T ++ s.map Prod.fst) S es = true -> Expr.closedList T S (Expr.gsubstList s es) = true
  | [], _, _, _ => rfl
  | _ :: _, _, _, hc => by
    simp only [Expr.closedList, Bool.and_eq_true] at hc
    simp only [Expr.gsubstList, Expr.closedList, Bool.and_eq_true]
    exact ⟨Expr.closed_gsubst hc.1, Expr.closedList_gsubst hc.2⟩
theorem Method.closed_gsubst {s : GSubst} : forall {M : Method} {T : List TVarName} {S : List VarName},
    M.closed (T ++ s.map Prod.fst) S = true -> (M.gsubst s).closed T S = true
  | .mk D T0 _ ps _, T, S, hc => by
    simp only [Method.closed, Bool.and_eq_true] at hc
    simp only [Method.gsubst, Method.closed, Bool.and_eq_true, dom_bounds_subst, names_subst]
    have hsub : Sub1 ((T ++ s.map Prod.fst) ++ dom D) ((T ++ dom D) ++ s.map Prod.fst) := by
      intro X hX
      simp only [listMem_iff, List.mem_append] at hX |-
      rcases hX with (hX | hX) | hX
      . exact Or.inl (Or.inl hX)
      . exact Or.inr hX
      . exact Or.inl (Or.inr hX)
    refine ⟨?_, Expr.closed_gsubst (Expr.closed_mono hc.2 hsub (fun _ h => h))⟩
    have e : (T0.subst s.ty :: cod (Bounds.subst s.ty D) ++ (ps.map (VarDecl.subst s.ty)).map VarDecl.T) =
        Ty.substList s.ty (T0 :: cod D ++ ps.map VarDecl.T) := by
      rw [cod_subst, params_T_subst]; simp only [Ty.substList, substList_app, List.cons_append]
    rw [e]
    exact Ty.ftvList_subst_all (all_contains_mono hc.1 hsub)
theorem Method.closedList_gsubst {s : GSubst} : forall {Ms : List Method} {T : List TVarName} {S : List VarName},
    Method.closedList (T ++ s.map Prod.fst) S Ms = true -> Method.closedList T S (Method.gsubstList s Ms) = true
  | [], _, _, _ => rfl
  | _ :: _, _, _, hc => by
    simp only [Method.closedList, Bool.and_eq_true] at hc
    simp only [Method.gsubstList, Method.closedList, Bool.and_eq_true]
    exact ⟨Method.closed_gsubst hc.1, Method.closedList_gsubst hc.2⟩
end

abbrev VNS (n : VSubst) (VB : List VarName) (TB : List TVarName) : Prop :=
  forall p, List.Mem p n -> p.2.expr.noShadow [] [] = true /\
    (forall y, List.Mem y p.2.expr.vbinders -> List.Mem y VB) /\ (forall X, List.Mem X p.2.expr.tbinders -> List.Mem X TB)

theorem VNS.filt {n : VSubst} {VB : List VarName} {TB : List TVarName} (h : VNS n VB TB) :
    VNS (n.filter fun p => p.1 != this) VB TB := fun p hp => h p (List.mem_filter.mp hp).1

mutual
theorem Expr.noShadow_vsubst {VB : List VarName} {TB : List TVarName} (hthis : Not (List.Mem this VB)) :
    forall {e : Expr} {n : VSubst} {Xs : List TVarName} {xs : List VarName}, e.noShadow Xs xs = true ->
    VNS n VB TB -> (forall y, List.Mem y xs -> Not (List.Mem y VB)) ->
    (forall y, List.Mem y e.vbinders -> Not (List.Mem y VB)) ->
    (forall X, List.Mem X Xs -> Not (List.Mem X TB)) -> (forall X, List.Mem X e.tbinders -> Not (List.Mem X TB)) ->
    (e.vsubst n).noShadow Xs xs = true
  | .var x, n, Xs, xs, _, hn, hxs, _, hXs, _ => by
    cases hl : List.lookup x n with
    | none => simp [Expr.vsubst, hl, Expr.noShadow]
    | some v =>
      simp only [Expr.vsubst, hl]
      have hv := hn (x, v) (lookup_mem hl)
      exact Expr.noShadow_mono hv.1 (fun X hX hm => absurd (hv.2.2 X hX) (hXs X hm))
        (fun y hy hm => absurd (hv.2.1 y hy) (hxs y hm))
  | .call _ _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.vbinders, listMem_iff, List.mem_append, Expr.tbinders] at h he hE
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.noShadow_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Expr.noShadowList_vsubst hthis h.2 hn hxs (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
  | .superCall _ _ _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.vbinders, listMem_iff, List.mem_append, Expr.tbinders] at h he hE
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.noShadow_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Expr.noShadowList_vsubst hthis h.2 hn hxs (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
  | .field _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.vsubst, Expr.noShadow]
    exact Expr.noShadow_vsubst hthis h hn hxs he hXs hE
  | .new _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => Expr.noShadowList_vsubst hthis h hn hxs he hXs hE
  | .newLocal _ _ _ _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.vbinders, listMem_iff, List.mem_append, Expr.tbinders] at h he hE
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.noShadowList_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Method.noShadowList_vsubst hthis h.2 hn.filt (fun y hy => hxs y (List.mem_filter.mp hy).1)
        (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
  | .ifInst _ _ x _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow, Bool.and_eq_true, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons,
      Expr.tbinders] at h he hE
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true]
    refine ⟨⟨⟨Expr.noShadow_vsubst hthis h.1.1.1 hn hxs (fun y hy => he y (Or.inl (Or.inl (Or.inr hy)))) hXs
      (fun X hX => hE X (Or.inl (Or.inl hX))), h.1.1.2⟩, ?_⟩,
      Expr.noShadow_vsubst hthis h.2 hn hxs (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
    refine Expr.noShadow_vsubst hthis h.1.2 hn ?_ (fun y hy => he y (Or.inl (Or.inr hy))) hXs
      (fun X hX => hE X (Or.inl (Or.inr hX)))
    intro y hy
    cases hy with
    | head => exact he x (Or.inl (Or.inl (Or.inl rfl)))
    | tail _ hy => exact hxs y hy
theorem Expr.noShadowList_vsubst {VB : List VarName} {TB : List TVarName} (hthis : Not (List.Mem this VB)) :
    forall {es : List Expr} {n : VSubst} {Xs : List TVarName} {xs : List VarName},
    Expr.noShadowList Xs xs es = true -> VNS n VB TB -> (forall y, List.Mem y xs -> Not (List.Mem y VB)) ->
    (forall y, List.Mem y (Expr.vbindersList es) -> Not (List.Mem y VB)) ->
    (forall X, List.Mem X Xs -> Not (List.Mem X TB)) ->
    (forall X, List.Mem X (Expr.tbindersList es) -> Not (List.Mem X TB)) ->
    Expr.noShadowList Xs xs (Expr.vsubstList n es) = true
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadowList, Bool.and_eq_true, Expr.vbindersList, listMem_iff, List.mem_append,
      Expr.tbindersList] at h he hE
    simp only [Expr.vsubstList, Expr.noShadowList, Bool.and_eq_true]
    exact ⟨Expr.noShadow_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Expr.noShadowList_vsubst hthis h.2 hn hxs (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
theorem Method.noShadow_vsubst {VB : List VarName} {TB : List TVarName} (hthis : Not (List.Mem this VB)) :
    forall {M : Method} {n : VSubst} {Xs : List TVarName} {xs : List VarName}, M.noShadow Xs xs = true ->
    VNS n VB TB -> (forall y, List.Mem y xs -> Not (List.Mem y VB)) ->
    (forall y, List.Mem y M.vbinders -> Not (List.Mem y VB)) ->
    (forall X, List.Mem X Xs -> Not (List.Mem X TB)) -> (forall X, List.Mem X M.tbinders -> Not (List.Mem X TB)) ->
    (M.vsubst n).noShadow Xs xs = true
  | .mk _ _ _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Method.noShadow, Bool.and_eq_true, Method.vbinders, listMem_iff, List.mem_append,
      Method.tbinders] at h he hE
    simp only [Method.vsubst, Method.noShadow, Bool.and_eq_true]
    refine ⟨h.1, Expr.noShadow_vsubst hthis h.2 hn ?_ (fun y hy => he y (Or.inr hy)) ?_ (fun X hX => hE X (Or.inr hX))⟩
    . intro y hy
      simp only [listMem_iff, List.mem_append, List.mem_cons] at hy
      rcases hy with (hy | hy) | hy
      . subst hy; exact hthis
      . exact hxs y hy
      . exact he y (Or.inl hy)
    . intro X hX
      exact (List.mem_append.mp hX).elim (hXs X) (fun hX => hE X (Or.inl hX))
theorem Method.noShadowList_vsubst {VB : List VarName} {TB : List TVarName} (hthis : Not (List.Mem this VB)) :
    forall {Ms : List Method} {n : VSubst} {Xs : List TVarName} {xs : List VarName},
    Method.noShadowList Xs xs Ms = true -> VNS n VB TB -> (forall y, List.Mem y xs -> Not (List.Mem y VB)) ->
    (forall y, List.Mem y (Method.vbindersList Ms) -> Not (List.Mem y VB)) ->
    (forall X, List.Mem X Xs -> Not (List.Mem X TB)) ->
    (forall X, List.Mem X (Method.tbindersList Ms) -> Not (List.Mem X TB)) ->
    Method.noShadowList Xs xs (Method.vsubstList n Ms) = true
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Method.noShadowList, Bool.and_eq_true, Method.vbindersList, listMem_iff, List.mem_append,
      Method.tbindersList] at h he hE
    simp only [Method.vsubstList, Method.noShadowList, Bool.and_eq_true]
    exact ⟨Method.noShadow_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Method.noShadowList_vsubst hthis h.2 hn hxs (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
end

end Funnelling
