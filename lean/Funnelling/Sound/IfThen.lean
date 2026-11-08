import Funnelling.Sound.RenTyping

open Funnelling.SoundSimp

namespace Funnelling.High

mutual
theorem Expr.noShadow_of_vsubst : forall {e : Expr} {n : VSubst} {Xs : List TVarName} {xs : List VarName},
    (e.vsubst n).noShadow Xs xs = true -> e.noShadow Xs xs = true
  | .var _, _, _, _, _ => rfl
  | .call e _ _ es, _, _, _, h => by
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true] at h |-
    exact And.intro (Expr.noShadow_of_vsubst h.1) (Expr.noShadowList_of_vsubst h.2)
  | .superCall e _ _ _ es, _, _, _, h => by
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true] at h |-
    exact And.intro (Expr.noShadow_of_vsubst h.1) (Expr.noShadowList_of_vsubst h.2)
  | .field e _, _, _, _, h => by
    simp only [Expr.vsubst, Expr.noShadow] at h |-
    exact Expr.noShadow_of_vsubst h
  | .new _ _ es, _, _, _, h => by
    simp only [Expr.vsubst, Expr.noShadow] at h |-
    exact Expr.noShadowList_of_vsubst h
  | .newLocal _ _ _ _ es Ms, _, _, _, h => by
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true] at h |-
    exact And.intro (Expr.noShadowList_of_vsubst h.1) (Method.noShadowList_of_vsubst h.2)
  | .ifInst e0 _ _ e1 e2, _, _, _, h => by
    simp only [Expr.vsubst, Expr.noShadow, Bool.and_eq_true] at h |-
    exact And.intro (And.intro (And.intro (Expr.noShadow_of_vsubst h.1.1.1) h.1.1.2) (Expr.noShadow_of_vsubst h.1.2))
      (Expr.noShadow_of_vsubst h.2)
theorem Expr.noShadowList_of_vsubst : forall {es : List Expr} {n : VSubst} {Xs : List TVarName} {xs : List VarName},
    Expr.noShadowList Xs xs (Expr.vsubstList n es) = true -> Expr.noShadowList Xs xs es = true
  | [], _, _, _, _ => rfl
  | e :: es, _, _, _, h => by
    simp only [Expr.vsubstList, Expr.noShadowList, Bool.and_eq_true] at h |-
    exact And.intro (Expr.noShadow_of_vsubst h.1) (Expr.noShadowList_of_vsubst h.2)
theorem Method.noShadow_of_vsubst : forall {M : Method} {n : VSubst} {Xs : List TVarName} {xs : List VarName},
    (M.vsubst n).noShadow Xs xs = true -> M.noShadow Xs xs = true
  | .mk _ _ _ _ e, _, _, _, h => by
    simp only [Method.vsubst, Method.noShadow, Bool.and_eq_true] at h |-
    exact And.intro h.1 (Expr.noShadow_of_vsubst h.2)
theorem Method.noShadowList_of_vsubst : forall {Ms : List Method} {n : VSubst} {Xs : List TVarName}
    {xs : List VarName}, Method.noShadowList Xs xs (Method.vsubstList n Ms) = true -> Method.noShadowList Xs xs Ms = true
  | [], _, _, _, _ => rfl
  | M :: Ms, _, _, _, h => by
    simp only [Method.vsubstList, Method.noShadowList, Bool.and_eq_true] at h |-
    exact And.intro (Method.noShadow_of_vsubst h.1) (Method.noShadowList_of_vsubst h.2)
end

mutual
theorem Expr.uniq_of_vsubst : forall {e : Expr} {n : VSubst}, (e.vsubst n).uniq -> e.uniq
  | .var _, _, _ => trivial
  | .call e _ _ es, _, h => by
    simp only [Expr.vsubst, Expr.uniq] at h |-
    exact And.intro (Expr.uniq_of_vsubst h.1) (Expr.uniqList_of_vsubst h.2)
  | .superCall e _ _ _ es, _, h => by
    simp only [Expr.vsubst, Expr.uniq] at h |-
    exact And.intro (Expr.uniq_of_vsubst h.1) (Expr.uniqList_of_vsubst h.2)
  | .field e _, _, h => by
    simp only [Expr.vsubst, Expr.uniq] at h |-
    exact Expr.uniq_of_vsubst h
  | .new _ _ es, _, h => by
    simp only [Expr.vsubst, Expr.uniq] at h |-
    exact Expr.uniqList_of_vsubst h
  | .newLocal _ _ _ _ es Ms, _, h => by
    simp only [Expr.vsubst, Expr.uniq] at h |-
    exact And.intro (Expr.uniqList_of_vsubst h.1) (Method.uniqList_of_vsubst h.2)
  | .ifInst e0 _ _ e1 e2, _, h => by
    simp only [Expr.vsubst, Expr.uniq] at h |-
    exact And.intro (Expr.uniq_of_vsubst h.1) (And.intro (Expr.uniq_of_vsubst h.2.1) (Expr.uniq_of_vsubst h.2.2))
theorem Expr.uniqList_of_vsubst : forall {es : List Expr} {n : VSubst},
    Expr.uniqList (Expr.vsubstList n es) -> Expr.uniqList es
  | [], _, _ => trivial
  | e :: es, _, h => by
    simp only [Expr.vsubstList, Expr.uniqList] at h |-
    exact And.intro (Expr.uniq_of_vsubst h.1) (Expr.uniqList_of_vsubst h.2)
theorem Method.uniq_of_vsubst : forall {M : Method} {n : VSubst}, (M.vsubst n).uniq -> M.uniq
  | .mk _ _ _ _ e, _, h => by
    simp only [Method.vsubst, Method.uniq] at h |-
    exact And.intro h.1 (And.intro h.2.1 (Expr.uniq_of_vsubst h.2.2))
theorem Method.uniqList_of_vsubst : forall {Ms : List Method} {n : VSubst},
    Method.uniqList (Method.vsubstList n Ms) -> Method.uniqList Ms
  | [], _, _ => trivial
  | M :: Ms, _, h => by
    simp only [Method.vsubstList, Method.uniqList] at h |-
    exact And.intro (Method.uniq_of_vsubst h.1) (Method.uniqList_of_vsubst h.2)
end

theorem all_not_contains_of {A : Type} [DecidableEq A] {l xs : List A} (h : forall x, List.Mem x l -> Not (List.Mem x xs)) :
    l.all (fun x => !(xs.contains x)) = true := by
  rw [List.all_eq_true]
  intro x hx
  simpa using h x hx

mutual
theorem Expr.noShadow_scope : forall {e : Expr} {Xs : List TVarName} {xs xs2 : List VarName},
    e.noShadow Xs xs = true -> (forall y, List.Mem y e.vbinders -> List.Mem y xs2 -> List.Mem y xs) ->
    e.noShadow Xs xs2 = true
  | .var _, _, _, _, _, _ => rfl
  | .call e _ _ es, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_scope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_scope h.2 (fun y hy => hs y (Or.inr hy)))
  | .superCall e _ _ _ es, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_scope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_scope h.2 (fun y hy => hs y (Or.inr hy)))
  | .field e _, _, _, _, h, hs => by
    simp only [Expr.noShadow] at h |-
    simp only [Expr.vbinders] at hs
    exact Expr.noShadow_scope h hs
  | .new _ _ es, _, _, _, h, hs => by
    simp only [Expr.noShadow] at h |-
    simp only [Expr.vbinders] at hs
    exact Expr.noShadowList_scope h hs
  | .newLocal _ _ _ _ es Ms, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append] at hs
    refine And.intro (Expr.noShadowList_scope h.1 (fun y hy => hs y (Or.inl hy))) ?_
    refine Method.noShadowList_scope h.2 (fun y hy hm => ?_)
    simp only [listMem_iff, List.mem_filter] at hm |-
    exact And.intro (hs y (Or.inr hy) hm.1) hm.2
  | .ifInst e0 _ x e1 e2, _, xs, xs2, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at h |-
    simp only [Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons] at hs
    have hx : Not (List.Mem x xs) := by have := h.1.1.2; simp at this; exact this
    refine And.intro (And.intro (And.intro (Expr.noShadow_scope h.1.1.1 (fun y hy => hs y (Or.inl (Or.inl (Or.inr hy)))))
      ?_) ?_) (Expr.noShadow_scope h.2 (fun y hy => hs y (Or.inr hy)))
    . have : Not (List.Mem x xs2) := fun hm => hx (hs x (Or.inl (Or.inl (Or.inl rfl))) hm)
      simpa using this
    . refine Expr.noShadow_scope h.1.2 (fun y hy hm => ?_)
      cases hm with
      | head => exact List.Mem.head _
      | tail _ hm => exact List.Mem.tail _ (hs y (Or.inl (Or.inr hy)) hm)
theorem Expr.noShadowList_scope : forall {es : List Expr} {Xs : List TVarName} {xs xs2 : List VarName},
    Expr.noShadowList Xs xs es = true -> (forall y, List.Mem y (Expr.vbindersList es) -> List.Mem y xs2 -> List.Mem y xs) ->
    Expr.noShadowList Xs xs2 es = true
  | [], _, _, _, _, _ => rfl
  | e :: es, _, _, _, h, hs => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at h |-
    simp only [Expr.vbindersList, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_scope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_scope h.2 (fun y hy => hs y (Or.inr hy)))
theorem Method.noShadow_scope : forall {M : Method} {Xs : List TVarName} {xs xs2 : List VarName},
    M.noShadow Xs xs = true -> (forall y, List.Mem y M.vbinders -> List.Mem y xs2 -> List.Mem y xs) ->
    M.noShadow Xs xs2 = true
  | .mk _ _ _ ps e, _, xs, xs2, h, hs => by
    simp only [Method.noShadow, Bool.and_eq_true] at h |-
    simp only [Method.vbinders, listMem_iff, List.mem_append] at hs
    refine And.intro (And.intro h.1.1 (all_not_contains_of (fun p hp hm =>
      not_mem_of_all_not_contains h.1.2 hp (hs p (Or.inl hp) hm)))) ?_
    refine Expr.noShadow_scope h.2 (fun y hy hm => ?_)
    simp only [listMem_iff, List.mem_append, List.mem_cons] at hm |-
    rcases hm with (hm | hm) | hm
    . exact Or.inl (Or.inl hm)
    . exact Or.inl (Or.inr (hs y (Or.inr hy) hm))
    . exact Or.inr hm
theorem Method.noShadowList_scope : forall {Ms : List Method} {Xs : List TVarName} {xs xs2 : List VarName},
    Method.noShadowList Xs xs Ms = true ->
    (forall y, List.Mem y (Method.vbindersList Ms) -> List.Mem y xs2 -> List.Mem y xs) ->
    Method.noShadowList Xs xs2 Ms = true
  | [], _, _, _, _, _ => rfl
  | M :: Ms, _, _, _, h, hs => by
    simp only [Method.noShadowList, Bool.and_eq_true] at h |-
    simp only [Method.vbindersList, listMem_iff, List.mem_append] at hs
    exact And.intro (Method.noShadow_scope h.1 (fun y hy => hs y (Or.inl hy)))
      (Method.noShadowList_scope h.2 (fun y hy => hs y (Or.inr hy)))
end

theorem value_declared {d : Decls} (hwf : WFDecls d) {v : Value} {T : Ty} (h : Typing d [] [] v.expr T) :
    exists k U, Declared d k /\ typeOf v = .cls k.name U := by
  cases v with
  | new C Gs vs =>
    cases value_new_declared hwf h with
    | intro D hD => exact Exists.intro (.dec D) (Exists.intro (GTy.tys Gs) (And.intro hD.1 (by simp [typeOf, K.name, hD.2])))
  | newLocal C Gs C' Gs' vs Ms =>
    simp only [Value.expr] at h
    rcases inv_local h rfl with ⟨w, hw⟩
    rcases consistent_unfold hw.cons with ⟨Fs', h⟩; cases h with
    | intro Ts' h => cases h with
      | intro es' h => cases h with
        | intro Ms' h => exact Exists.intro _ (Exists.intro (GTy.tys Gs) (And.intro h.1 (by simp [typeOf, K.name])))

theorem pres_ifThen' {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {C' : ClassName}
    {Ts Ts' : List Ty} {x : VarName} {e1 e1' e2 : Expr} {v : Value} {T : Ty} (hs : Sub d [] (typeOf v) (.cls C' Ts'))
    (hf : Fresh e1 e1') (hdf : VSubstDefined [x] e1') (ha : WFExpr (.ifInst v.expr (.cls C' Ts) x e1 e2))
    (ha' : WFExpr (e1'.vsubst [(x, v)])) (h : Typing d [] [] (.ifInst v.expr (.cls C' Ts) x e1 e2) T) :
    Typing d [] [] (e1'.vsubst [(x, v)]) T := by
  rcases inv_if h rfl with ⟨w, hw⟩
  have vt := value_typing hwf hw.ty0
  have hsv : Sub d [] (typeOf v) w.T0 := by
    rcases vt.1 with e | e
    . rw [e]; exact Sub.subRefl
    . exact e.1
  rcases value_declared hwf vt.2.1 with ⟨k, h⟩; cases h with
  | intro U hU =>
    have hk1 := vt.2.2
    rw [hU.2] at hsv hs hk1
    have hc := cast_runtime hwf hok hd hU.1 hw.cast hsv hs hw.kind hk1
    rw [<- hU.2] at hc
    have hvT : Typing d [] [] v.expr (.cls C' Ts) := Typing.subs vt.2.1 hw.kind hc
    have hn := ha.2.2.2.2.1
    simp only [Expr.noShadow, Bool.and_eq_true] at hn
    have hu := WFExpr.uniq ha
    simp only [Expr.uniq] at hu
    have ht := WFExpr.noThis ha
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht
    have hn' : e1'.noShadow [] [x] = true :=
      Expr.noShadow_scope (Expr.noShadow_of_vsubst ha'.2.2.2.2.1)
        (fun y hy hm => absurd hm (hdf y hy))
    have ht' : NoThis e1' := noThis_of_vsubst (WFExpr.noThis ha')
    have hu' : e1'.uniq := Expr.uniq_of_vsubst (WFExpr.uniq ha')
    have hT : forall X, List.Mem X (Ty.cls C' Ts).ftv -> List.Mem X ([] : List TVarName) :=
      fun X hX => Kind.ftv hw.kind X hX
    have env : REnv [] [] [] [] [{ T := .cls C' Ts, x := x }] [{ T := .cls C' Ts, x := x }] [] [x] [x] :=
      { bD := fun _ h => by cases h
        dX := fun _ h => by cases h
        dT := fun _ h => by cases h
        g := fun z U hl => by rw [rn_nil, Ty.ren_id (fun _ _ => rn_nil)]; exact hl
        gT := fun y hy X hX => by
          cases hy with
          | head => exact hT X hX
          | tail _ h => cases h
        gN := by simp [gdom]
        gx := fun y hy => hy
        gx' := fun y hy => hy
        kv := fun _ h => by cases h }
    have ty1 := hw.ty1
    simp only [List.nil_append] at ty1
    have hr := Typing.ren hwf hok hd ty1 hf.1 env hn.1.2 hn' ht.1.2 ht' hu.2.1 hu'
    rw [Ty.ren_id (fun _ _ => rn_nil)] at hr
    have hsub := Typing.vsub hr (n := [(x, v)]) (Xs := []) (xs := [x]) (xs' := [])
      (fun y v' U hy hl => by
        by_cases hyx : y = x
        . subst hyx
          simp [List.lookup] at hy
          simp [Gamma.lookup] at hl
          rw [<- hy, <- hl]
          exact hvT
        . rw [lookup_cons_ne hyx] at hy; cases hy)
      (fun p hp => by
        cases hp with
        | head => exact And.intro hn.1.1.1 (And.intro ht.1.1.2 hu.1)
        | tail _ h => cases h)
      (fun y hy => by simpa using hdf y hy) (by simp [gdom]) (fun y hy => hy)
      (fun y hy => by simp [gsub, gdom] at hy) hn' ha'.2.2.2.2.1 ht' hu'
    have eg : gsub [(x, v)] [{ T := .cls C' Ts, x := x }] = [] := by simp [gsub]
    rw [eg] at hsub
    exact hw.up.typing hsub

end Funnelling.High
