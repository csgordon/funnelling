import Funnelling.Sound.Progress

open Funnelling.SoundSimp

namespace Funnelling.High

def KQ' (Ms : List Method) (Fs : List Funnel) : Prop := (Ms.map Method.name).Nodup /\ (domF Fs).Nodup /\
  forall M, List.Mem M Ms -> (M.params.map VarDecl.x).Nodup /\ (dom M.bounds).Nodup /\
    Not (List.Mem this (M.params.map VarDecl.x))

abbrev KQ (k : K) : Prop := KQ' k.Ms k.Fs

theorem K.Ms_loc {C : ClassName} {Fs : List Funnel} {C' : ClassName} {Ts : List Ty} {es : List Expr} {Ms : List Method} :
    (K.loc C Fs C' Ts es Ms).Ms = Ms := rfl

theorem K.Fs_loc {C : ClassName} {Fs : List Funnel} {C' : ClassName} {Ts : List Ty} {es : List Expr} {Ms : List Method} :
    (K.loc C Fs C' Ts es Ms).Fs = Fs := rfl

theorem KQ'.vsubst {n : VSubst} {Ms : List Method} {Fs : List Funnel} (h : KQ' Ms Fs) :
    KQ' (Method.vsubstList n Ms) Fs := by
  unfold KQ' at h ⊢
  refine ⟨by rw [names_vsubst]; exact h.1, h.2.1, fun M hM => ?_⟩
  rcases vsubstList_mem hM with ⟨M0, hM0, e⟩
  subst e
  cases M0 with
  | mk D T m ps b => exact h.2.2 (Method.mk D T m ps b) hM0

abbrev VLoc (n : VSubst) : Prop := forall p, List.Mem p n -> forall k, List.Mem k p.2.expr.locals -> KQ k

mutual
theorem Expr.kq_vsubst : forall {e : Expr} {n : VSubst}, (forall k, List.Mem k e.locals -> KQ k) -> VLoc n ->
    forall k, List.Mem k (e.vsubst n).locals -> KQ k
  | .var x, n, _, hn => by
    intro k hk
    cases hl : List.lookup x n with
    | none => simp [Expr.vsubst, hl, Expr.locals] at hk
    | some v => simp only [Expr.vsubst, hl] at hk; exact hn (x, v) (lookup_mem hl) k hk
  | .call _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h ⊢
    exact ⟨Expr.kq_vsubst h.1 hn, Expr.kq_vsubstList h.2 hn⟩
  | .superCall _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h ⊢
    exact ⟨Expr.kq_vsubst h.1 hn, Expr.kq_vsubstList h.2 hn⟩
  | .field _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals] at h ⊢
    exact Expr.kq_vsubst h hn
  | .new _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals] at h ⊢
    exact Expr.kq_vsubstList h hn
  | .newLocal _ _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals, listMem_iff, List.mem_append, List.mem_cons, or_imp, forall_and,
      forall_eq] at h ⊢
    exact ⟨KQ'.vsubst h.1, Expr.kq_vsubstList h.2.1 hn,
      Method.kq_vsubstList h.2.2 (fun p hp => hn p (List.mem_filter.mp hp).1)⟩
  | .ifInst _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at h ⊢
    exact ⟨⟨Expr.kq_vsubst h.1.1 hn, Expr.kq_vsubst h.1.2 hn⟩, Expr.kq_vsubst h.2 hn⟩
theorem Expr.kq_vsubstList : forall {es : List Expr} {n : VSubst},
    (forall k, List.Mem k (Expr.localsList es) -> KQ k) -> VLoc n ->
    forall k, List.Mem k (Expr.localsList (Expr.vsubstList n es)) -> KQ k
  | [], _, _, _ => by intro k hk; simp [Expr.vsubstList, Expr.localsList] at hk
  | _ :: _, _, h, hn => by
    simp only [Expr.vsubstList, Expr.localsList, listMem_iff, List.mem_append, or_imp, forall_and] at h ⊢
    exact ⟨Expr.kq_vsubst h.1 hn, Expr.kq_vsubstList h.2 hn⟩
theorem Method.kq_vsubst : forall {M : Method} {n : VSubst}, (forall k, List.Mem k M.locals -> KQ k) -> VLoc n ->
    forall k, List.Mem k (M.vsubst n).locals -> KQ k
  | .mk _ _ _ _ _, _, h, hn => by
    simp only [Method.vsubst, Method.locals] at h ⊢
    exact Expr.kq_vsubst h hn
theorem Method.kq_vsubstList : forall {Ms : List Method} {n : VSubst},
    (forall k, List.Mem k (Method.localsList Ms) -> KQ k) -> VLoc n ->
    forall k, List.Mem k (Method.localsList (Method.vsubstList n Ms)) -> KQ k
  | [], _, _, _ => by intro k hk; simp [Method.vsubstList, Method.localsList] at hk
  | _ :: _, _, h, hn => by
    simp only [Method.vsubstList, Method.localsList, listMem_iff, List.mem_append, or_imp, forall_and] at h ⊢
    exact ⟨Method.kq_vsubst h.1 hn, Method.kq_vsubstList h.2 hn⟩
end

mutual
theorem Expr.ifVars_vsubst {z : VarName} : forall {e : Expr} {n : VSubst}, Not (List.Mem z e.ifVars) ->
    (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.ifVars)) -> Not (List.Mem z (e.vsubst n).ifVars)
  | .var x, n, _, hn => by
    cases hl : List.lookup x n with
    | none => simp [Expr.vsubst, hl, Expr.ifVars]
    | some v => simp only [Expr.vsubst, hl]; exact hn (x, v) (lookup_mem hl)
  | .call _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Expr.ifVars_vsubst h.1 hn, Expr.ifVarsList_vsubst h.2 hn⟩
  | .superCall _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Expr.ifVars_vsubst h.1 hn, Expr.ifVarsList_vsubst h.2 hn⟩
  | .field _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars] at h ⊢
    exact Expr.ifVars_vsubst h hn
  | .new _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars] at h ⊢
    exact Expr.ifVarsList_vsubst h hn
  | .newLocal _ _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Expr.ifVarsList_vsubst h.1 hn, Method.ifVarsList_vsubst h.2 (fun p hp => hn p (List.mem_filter.mp hp).1)⟩
  | .ifInst _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.ifVars, listMem_iff, List.mem_append, List.mem_cons, not_or] at h ⊢
    exact ⟨⟨⟨h.1.1.1, Expr.ifVars_vsubst h.1.1.2 hn⟩, Expr.ifVars_vsubst h.1.2 hn⟩, Expr.ifVars_vsubst h.2 hn⟩
theorem Expr.ifVarsList_vsubst {z : VarName} : forall {es : List Expr} {n : VSubst},
    Not (List.Mem z (Expr.ifVarsList es)) -> (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.ifVars)) ->
    Not (List.Mem z (Expr.ifVarsList (Expr.vsubstList n es)))
  | [], _, _, _ => by simp [Expr.vsubstList, Expr.ifVarsList]
  | _ :: _, _, h, hn => by
    simp only [Expr.vsubstList, Expr.ifVarsList, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Expr.ifVars_vsubst h.1 hn, Expr.ifVarsList_vsubst h.2 hn⟩
theorem Method.ifVars_vsubst {z : VarName} : forall {M : Method} {n : VSubst}, Not (List.Mem z M.ifVars) ->
    (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.ifVars)) -> Not (List.Mem z (M.vsubst n).ifVars)
  | .mk _ _ _ _ _, _, h, hn => by
    simp only [Method.vsubst, Method.ifVars] at h ⊢
    exact Expr.ifVars_vsubst h hn
theorem Method.ifVarsList_vsubst {z : VarName} : forall {Ms : List Method} {n : VSubst},
    Not (List.Mem z (Method.ifVarsList Ms)) -> (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.ifVars)) ->
    Not (List.Mem z (Method.ifVarsList (Method.vsubstList n Ms)))
  | [], _, _, _ => by simp [Method.vsubstList, Method.ifVarsList]
  | _ :: _, _, h, hn => by
    simp only [Method.vsubstList, Method.ifVarsList, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Method.ifVars_vsubst h.1 hn, Method.ifVarsList_vsubst h.2 hn⟩
end

mutual
theorem Expr.vbinders_vsubst_not {z : VarName} : forall {e : Expr} {n : VSubst}, Not (List.Mem z e.vbinders) ->
    (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.vbinders)) -> Not (List.Mem z (e.vsubst n).vbinders)
  | .var x, n, _, hn => by
    cases hl : List.lookup x n with
    | none => simp [Expr.vsubst, hl, Expr.vbinders]
    | some v => simp only [Expr.vsubst, hl]; exact hn (x, v) (lookup_mem hl)
  | .call _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.vbinders, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Expr.vbinders_vsubst_not h.1 hn, Expr.vbindersList_vsubst_not h.2 hn⟩
  | .superCall _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.vbinders, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Expr.vbinders_vsubst_not h.1 hn, Expr.vbindersList_vsubst_not h.2 hn⟩
  | .field _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.vbinders] at h ⊢
    exact Expr.vbinders_vsubst_not h hn
  | .new _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.vbinders] at h ⊢
    exact Expr.vbindersList_vsubst_not h hn
  | .newLocal _ _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.vbinders, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Expr.vbindersList_vsubst_not h.1 hn,
      Method.vbindersList_vsubst_not h.2 (fun p hp => hn p (List.mem_filter.mp hp).1)⟩
  | .ifInst _ _ _ _ _, _, h, hn => by
    simp only [Expr.vsubst, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at h ⊢
    exact ⟨⟨⟨h.1.1.1, Expr.vbinders_vsubst_not h.1.1.2 hn⟩, Expr.vbinders_vsubst_not h.1.2 hn⟩,
      Expr.vbinders_vsubst_not h.2 hn⟩
theorem Expr.vbindersList_vsubst_not {z : VarName} : forall {es : List Expr} {n : VSubst},
    Not (List.Mem z (Expr.vbindersList es)) -> (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.vbinders)) ->
    Not (List.Mem z (Expr.vbindersList (Expr.vsubstList n es)))
  | [], _, _, _ => by simp [Expr.vsubstList, Expr.vbindersList]
  | _ :: _, _, h, hn => by
    simp only [Expr.vsubstList, Expr.vbindersList, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Expr.vbinders_vsubst_not h.1 hn, Expr.vbindersList_vsubst_not h.2 hn⟩
theorem Method.vbinders_vsubst_not {z : VarName} : forall {M : Method} {n : VSubst}, Not (List.Mem z M.vbinders) ->
    (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.vbinders)) -> Not (List.Mem z (M.vsubst n).vbinders)
  | .mk _ _ _ _ _, _, h, hn => by
    simp only [Method.vsubst, Method.vbinders, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨h.1, Expr.vbinders_vsubst_not h.2 hn⟩
theorem Method.vbindersList_vsubst_not {z : VarName} : forall {Ms : List Method} {n : VSubst},
    Not (List.Mem z (Method.vbindersList Ms)) -> (forall p, List.Mem p n -> Not (List.Mem z p.2.expr.vbinders)) ->
    Not (List.Mem z (Method.vbindersList (Method.vsubstList n Ms)))
  | [], _, _, _ => by simp [Method.vsubstList, Method.vbindersList]
  | _ :: _, _, h, hn => by
    simp only [Method.vsubstList, Method.vbindersList, listMem_iff, List.mem_append, not_or] at h ⊢
    exact ⟨Method.vbinders_vsubst_not h.1 hn, Method.vbindersList_vsubst_not h.2 hn⟩
end

mutual
theorem Expr.closed_vsubst : forall {e : Expr} {n : VSubst} {T : List TVarName} {S : List VarName},
    e.closed T (S ++ n.map Prod.fst) = true -> (forall p, List.Mem p n -> p.2.expr.closed [] [] = true) ->
    (e.vsubst n).closed T S = true
  | .var x, n, T, S, hc, hn => by
    cases hl : List.lookup x n with
    | none =>
      simp only [Expr.vsubst, hl, Expr.closed] at hc ⊢
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
    simp only [Expr.closed] at hc
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
    simp only [listMem_iff, List.mem_append, List.mem_cons] at hy ⊢
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
    simp only [listMem_iff, List.mem_append, List.mem_cons] at hy ⊢
    rcases hy with (hy | hy | hy) | hy
    . exact Or.inl (Or.inl (Or.inl hy))
    . exact Or.inl (Or.inl (Or.inr hy))
    . by_cases hyt : y = this
      . exact Or.inl (Or.inl (Or.inl hyt))
      . refine Or.inr ?_
        rcases List.mem_map.mp hy with ⟨p, hp, e⟩
        subst e
        exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hp, by simpa using hyt⟩)
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
      have h1 := Expr.noShadow_tscope (Xs2 := Xs) hv.1 (fun X hX hm => absurd (hv.2.2 X hX) (hXs X hm))
      exact Expr.noShadow_scope h1 (fun y hy hm => absurd (hv.2.1 y hy) (hxs y hm))
  | .call _ _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at he
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hE
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.noShadow_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Expr.noShadowList_vsubst hthis h.2 hn hxs (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
  | .superCall _ _ _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at he
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hE
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.noShadow_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Expr.noShadowList_vsubst hthis h.2 hn hxs (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
  | .field _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow] at h
    simp only [Expr.vbinders] at he
    simp only [Expr.tbinders] at hE
    simp only [Expr.vsubst, Expr.noShadow]
    exact Expr.noShadow_vsubst hthis h hn hxs he hXs hE
  | .new _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow] at h
    simp only [Expr.vbinders] at he
    simp only [Expr.tbinders] at hE
    simp only [Expr.vsubst, Expr.noShadow]
    exact Expr.noShadowList_vsubst hthis h hn hxs he hXs hE
  | .newLocal _ _ _ _ _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at he
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hE
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.noShadowList_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Method.noShadowList_vsubst hthis h.2 hn.filt (fun y hy => hxs y (List.mem_filter.mp hy).1)
        (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
  | .ifInst _ _ x _ _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h
    simp only [Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons] at he
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hE
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
    simp only [Expr.noShadowList, Bool.and_eq_true] at h
    simp only [Expr.vbindersList, listMem_iff, List.mem_append] at he
    simp only [Expr.tbindersList, listMem_iff, List.mem_append] at hE
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
    simp only [Method.noShadow, Bool.and_eq_true] at h
    simp only [Method.vbinders, listMem_iff, List.mem_append] at he
    simp only [Method.tbinders, listMem_iff, List.mem_append] at hE
    simp only [Method.vsubst, Method.noShadow, Bool.and_eq_true]
    refine ⟨h.1, Expr.noShadow_vsubst hthis h.2 hn ?_ (fun y hy => he y (Or.inr hy)) ?_ (fun X hX => hE X (Or.inr hX))⟩
    . intro y hy
      simp only [listMem_iff, List.mem_append, List.mem_cons] at hy
      rcases hy with (hy | hy) | hy
      . subst hy; exact hthis
      . exact hxs y hy
      . exact he y (Or.inl hy)
    . intro X hX
      simp only [listMem_iff, List.mem_append] at hX
      rcases hX with hX | hX
      . exact hXs X hX
      . exact hE X (Or.inl hX)
theorem Method.noShadowList_vsubst {VB : List VarName} {TB : List TVarName} (hthis : Not (List.Mem this VB)) :
    forall {Ms : List Method} {n : VSubst} {Xs : List TVarName} {xs : List VarName},
    Method.noShadowList Xs xs Ms = true -> VNS n VB TB -> (forall y, List.Mem y xs -> Not (List.Mem y VB)) ->
    (forall y, List.Mem y (Method.vbindersList Ms) -> Not (List.Mem y VB)) ->
    (forall X, List.Mem X Xs -> Not (List.Mem X TB)) ->
    (forall X, List.Mem X (Method.tbindersList Ms) -> Not (List.Mem X TB)) ->
    Method.noShadowList Xs xs (Method.vsubstList n Ms) = true
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, _, _, _, h, hn, hxs, he, hXs, hE => by
    simp only [Method.noShadowList, Bool.and_eq_true] at h
    simp only [Method.vbindersList, listMem_iff, List.mem_append] at he
    simp only [Method.tbindersList, listMem_iff, List.mem_append] at hE
    simp only [Method.vsubstList, Method.noShadowList, Bool.and_eq_true]
    exact ⟨Method.noShadow_vsubst hthis h.1 hn hxs (fun y hy => he y (Or.inl hy)) hXs (fun X hX => hE X (Or.inl hX)),
      Method.noShadowList_vsubst hthis h.2 hn hxs (fun y hy => he y (Or.inr hy)) hXs (fun X hX => hE X (Or.inr hX))⟩
end

end Funnelling.High
