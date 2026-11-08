import Funnelling.Sound.FreshMain

open Funnelling.SoundSimp

namespace Funnelling.High

theorem nodup_map_inj {A B : Type} {f : A -> B} : forall {l : List A}, (l.map f).Nodup ->
    forall {x y : A}, List.Mem x l -> List.Mem y l -> f x = f y -> x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, hn, x, y, hx, hy, he => by
    simp only [List.map_cons, List.nodup_cons] at hn
    cases hx with
    | head =>
      cases hy with
      | head => rfl
      | tail _ hy => exact absurd (he ▸ List.mem_map_of_mem hy) hn.1
    | tail _ hx =>
      cases hy with
      | head => exact absurd (he.symm ▸ List.mem_map_of_mem hx) hn.1
      | tail _ hy => exact nodup_map_inj hn.2 hx hy he

theorem Declared.dec_mem {d : Decls} {D : Dec} (h : Declared d (.dec D)) : List.Mem D d := by
  cases h with
  | dec h => exact h

theorem dec_unique {d : Decls} (hwf : WFDecls d) {D1 D2 : Dec} (he : D1.C = D2.C) (h1 : Declared d (.dec D1))
    (h2 : Declared d (.dec D2)) : D1 = D2 := by
  have := nodup_map_inj hwf.1 (classes_mem_dec h1.dec_mem) (classes_mem_dec h2.dec_mem) he
  cases this; rfl

theorem find_unique {A : Type} {p : A -> Bool} {x : A} : forall {l : List A},
    (forall y, List.Mem y l -> p y = true -> y = x) -> List.Mem x l -> p x = true -> l.find? p = some x
  | [], _, hx, _ => by cases hx
  | a :: l, h, hx, hp => by
    by_cases ha : p a = true
    . rw [List.find?_cons_of_pos ha, h a (List.Mem.head _) ha]
    . rw [List.find?_cons_of_neg ha]
      cases hx with
      | head => exact absurd hp ha
      | tail _ hx => exact find_unique (fun y hy hpy => h y (List.Mem.tail _ hy) hpy) hx hp

theorem findDec_self {d : Decls} (hwf : WFDecls d) {D : Dec} (h : List.Mem D d) : findDec d D.C = some D := by
  apply find_unique
  . intro y hy hp
    exact dec_unique hwf (by simpa using hp) (.dec hy) (.dec h)
  . exact h
  . simp

theorem fields_nodup {d : Decls} (hwf : WFDecls d) {D : Dec} (h : List.Mem D d) : (D.Ss.map Slot.f).Nodup := by
  have h2 := hwf.2.1 D h
  simp only [superChain, findDec_self hwf h] at h2
  by_cases ho : (D.C == Object) = true
  . simp_all
  . simp only [ho] at h2
    exact nodup_append_left h2

theorem zip_unique {A B : Type} : forall {xs : List A} {ys : List B} {x : A} {y y' : B}, xs.Nodup ->
    List.Mem (x, y) (xs.zip ys) -> List.Mem (x, y') (xs.zip ys) -> y = y'
  | [], _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, _, h, _ => by cases h
  | a :: xs, b :: ys, x, y, y', hn, h1, h2 => by
    cases h1 with
    | head =>
      cases h2 with
      | head => rfl
      | tail _ h2 => exact absurd (List.of_mem_zip h2).1 (List.nodup_cons.mp hn).1
    | tail _ h1 =>
      cases h2 with
      | head => exact absurd (List.of_mem_zip h1).1 (List.nodup_cons.mp hn).1
      | tail _ h2 => exact zip_unique (List.nodup_cons.mp hn).2 h1 h2

theorem zip_mem_fst {A B : Type} {xs : List A} {ys : List B} {x : A} {y : B} (h : List.Mem (x, y) (xs.zip ys)) :
    List.Mem x xs := (List.of_mem_zip h).1

theorem FreshM.name {M : Method} {D : Bounds} {T : Ty} {m : MethName} {ps : List VarDecl} {e : Expr}
    (h : FreshM M (.mk D T m ps e)) : M.name = m := by
  cases M with
  | mk D' T' m' ps' e' => exact (RenM.body h.1).2.2.2

theorem FreshM.mem_names {M : Method} {Ms : List Method} {D T m ps e} (hM : List.Mem M Ms)
    (h : FreshM M (.mk D T m ps e)) : List.Mem m (Ms.map Method.name) :=
  FreshM.name h ▸ List.mem_map_of_mem hM

theorem uniqList_mem {M : Method} : forall {Ms : List Method}, List.Mem M Ms -> Method.uniqList Ms -> M.uniq
  | _, .head _, hu => by simp only [Method.uniqList] at hu; exact hu.1
  | _, .tail _ h, hu => by simp only [Method.uniqList] at hu; exact uniqList_mem h hu.2

theorem vbindersListM_mem {M : Method} {x : VarName} : forall {Ms : List Method}, List.Mem M Ms ->
    List.Mem x M.vbinders -> List.Mem x (Method.vbindersList Ms)
  | _, .head _, hx => by simp only [Method.vbindersList, listMem_iff, List.mem_append]; exact Or.inl hx
  | _, .tail _ h, hx => by simp only [Method.vbindersList, listMem_iff, List.mem_append]; exact Or.inr (vbindersListM_mem h hx)

theorem closedList_vals {T : List TVarName} {S : List VarName} : forall {vs : List Value},
    Expr.closedList T S (Value.exprs vs) = true -> forall v, List.Mem v vs -> v.expr.closed T S = true
  | [], _, _, h => by cases h
  | w :: vs, h, v, hv => by
    simp only [Value.exprs, Expr.closedList, Bool.and_eq_true] at h
    cases hv with
    | head => exact h.1
    | tail _ hv => exact closedList_vals h.2 v hv

theorem closed_cons_vals {v0 : Value} {vs : List Value} (h0 : v0.expr.closed [] [] = true)
    (hs : Expr.closedList [] [] (Value.exprs vs) = true) :
    forall v, List.Mem v (v0 :: vs) -> v.expr.closed [] [] = true := by
  intro v hv
  cases hv with
  | head => exact h0
  | tail _ hv => exact closedList_vals hs v hv

theorem det_base {d : Decls} (hwf : WFDecls d) {a a' b1 b2 : Expr} (ha : WFExpr a) (hw1 : WFExpr b1)
    (hw2 : WFExpr b2) (h1 : BaseStep d a b1) (h2 : BaseStep d a' b2) (he : a = a') : Fresh b1 b2 := by
  revert he
  cases h1 <;> cases h2 <;> simp only [Function.Injective.eq_iff (f := Value.expr) (fun _ _ => Value.expr_inj),
    Function.Injective.eq_iff (f := GTy.tys) (fun _ _ => GTy.tys_inj), Function.Injective.eq_iff (f := Value.exprs)
    (fun _ _ => Value.exprs_inj), Expr.field.injEq, Expr.ifInst.injEq, Expr.call.injEq, Expr.superCall.injEq,
    Ty.cls.injEq, Value.new.injEq, Value.newLocal.injEq, reduceCtorEq, false_and, false_implies, and_imp] <;>
    intros <;> subst_vars <;> injections <;> subst_vars <;>
    (try obtain rfl := dec_unique hwf ‹Dec.C _ = Dec.C _› ‹_› ‹_›) <;>
    (try obtain ⟨rfl, rfl⟩ := List.append_inj ‹_ ++ _ = _ ++ _› (by omega)) <;>
    first
    | exact Fresh.refl _
    | exact absurd (zip_mem_fst ‹List.Mem (_, _) _›) ‹_›
    | exact absurd (FreshM.mem_names ‹_› ‹_›) ‹_›
    | exact absurd ‹Sub _ _ _ _› (fun h => ‹¬exists _, _› ⟨_, h⟩)
    | skip
  case simpleFieldFound.simpleFieldFound =>
    rename_i hm _ _ _ hm' _
    exact zip_unique (fields_nodup hwf ‹Declared d _›.dec_mem) hm hm' ▸ Fresh.refl _
  case ifThen.ifThen =>
    rename_i hf2 hd2 hd hf _
    have hn := ha.2.2.2.2.1
    have hu := ha.uniq
    have ht := ha.noThis
    have hc := ha.2.2.2.2.2.2
    simp only [Expr.noShadow, Expr.closed, Bool.and_eq_true, NoThis, Expr.vbinders, listMem_iff, List.mem_append,
      List.mem_cons, not_or] at hn ht hc
    exact fresh_if hf hf2 hd hd2 hw1 hw2 hn.1.2 hu.2.1 ht.1.2 hc.1.1.1
  case ifThen.ifElse => exact (‹¬exists Ts', Sub d [] _ (.cls _ Ts')› ⟨_, ‹_›⟩).elim
  case ifElse.ifThen => exact (‹¬exists Ts', Sub d [] _ (.cls _ Ts')› ⟨_, ‹_›⟩).elim
  case simpleFound.simpleFound =>
    rename_i hD hM hN hN' hgs hvs _ _ _ _ _ _ _ _ _ _ hF2 hG2' hN2' hp2 hvs2 hF hG hG' hp _ hM2 _ hN2 hgs2 _
    obtain rfl := nodup_map_inj (hwf.2.2.1 _ (classes_mem_dec hD.dec_mem)) hM hM2
      (by rw [FreshM.name hF, FreshM.name hF2])
    have hMf := hwf.method hD.dec_mem hM
    have hc := ha.2.2.2.2.2.2
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have hvals := closed_cons_vals hc.1.1 hc.2
    exact And.intro
      (renE_meth hF.2 hF2.1 hMf.1 hMf.2.1 hMf.2.2 hG hG' hG2' hp hp2 hN hN2 hN' hN2' hgs hgs2 hvs hvs2
        hw1.2.2.2.2.2.2 hvals)
      (renE_meth hF2.2 hF.1 hMf.1 hMf.2.1 hMf.2.2 hG hG2' hG' hp2 hp hN2 hN hN2' hN' hgs2 hgs hvs2 hvs
        hw2.2.2.2.2.2.2 hvals)
  case innerFound.innerFound =>
    rename_i hN hN' hgs hvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM2 hF2 hG2 hp2 hN2 hN2' hgs2 hvs2 hF hG hp hM
    obtain rfl := nodup_map_inj (ha.1 _ (List.mem_append_left _ (List.Mem.head _))) hM hM2
      (by rw [FreshM.name hF, FreshM.name hF2])
    have hu := ha.uniq
    have ht := ha.noThis
    have hn := ha.2.2.2.2.1
    have hc := ha.2.2.2.2.2.2
    simp only [NoThis, Expr.vbinders, Value.expr, listMem_iff, List.mem_append, not_or, Expr.noShadow,
      Bool.and_eq_true] at ht hn
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have hvals := closed_cons_vals hc.1.1 hc.2
    have hMu := uniqList_mem hM hu.1.2
    have hMt : NoThisM _ := fun h => ht.1.2 (vbindersListM_mem hM h)
    have hMn : Method.noShadow (dom []) [] _ = true := noShadowListM_mem hM hn.1.2
    exact And.intro
      (renE_meth (B := []) (Gs := []) hF.2 hF2.1 hMu hMt hMn rfl hG hG2 hp hp2 hN hN2 hN' hN2' hgs hgs2 hvs hvs2
        hw1.2.2.2.2.2.2 hvals)
      (renE_meth (B := []) (Gs := []) hF2.2 hF.1 hMu hMt hMn rfl hG2 hG hp2 hp hN2 hN hN2' hN' hgs2 hgs hvs2 hvs
        hw2.2.2.2.2.2.2 hvals)

theorem determinismHigh {d : Decls} {e e1 e2 : Expr} (hwf : WFDecls d) (he : WFExpr e) (h1 : Reduces d e e1)
    (h2 : Reduces d e e2) : Fresh e1 e2 := by
  rcases Step.toBase h1.1 with ⟨E, h⟩
  rcases h with ⟨a, h⟩
  rcases h with ⟨a', h⟩
  have hb := h.2.2
  have hna : NonValue a := Step.not_value hb.toStep
  have h2s := h2.1
  rw [h.1] at h2s he
  rcases Step.decomp h2s hna with ⟨a2, h3⟩
  have hb2 := Step.strip h3.1 hb
  have hw1 : WFExpr a' := by have := h1.2; rw [h.2.1] at this; exact WFExpr.plug this
  have hw2 : WFExpr a2 := by have := h2.2; rw [h3.2] at this; exact WFExpr.plug this
  rw [h.2.1, h3.2]
  exact Fresh.plug (det_base hwf (WFExpr.plug he) hw1 hw2 hb hb2 rfl) E

end Funnelling.High
