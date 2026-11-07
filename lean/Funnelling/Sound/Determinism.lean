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

theorem dec_unique {d : Decls} (hwf : WFDecls d) {D1 D2 : Dec} (h1 : List.Mem D1 d) (h2 : List.Mem D2 d)
    (he : D1.C = D2.C) : D1 = D2 := by
  have := nodup_map_inj hwf.1 (classes_mem_dec h1) (classes_mem_dec h2) he
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
    exact dec_unique hwf hy h (by simpa using hp)
  . exact h
  . simp

theorem fields_nodup {d : Decls} (hwf : WFDecls d) {D : Dec} (h : List.Mem D d) : (D.Ss.map Slot.f).Nodup := by
  have h2 := hwf.2.1 D h
  simp only [superChain, findDec_self hwf h] at h2
  by_cases ho : (D.C == Object) = true
  . simp only [ho, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h2
    exact h2
  . simp only [ho] at h2
    simp only [Bool.false_eq_true, if_false, List.flatMap_cons] at h2
    exact nodup_append_left h2

theorem zip_unique {A B : Type} : forall {xs : List A} {ys : List B} {x : A} {y y' : B}, xs.Nodup ->
    List.Mem (x, y) (xs.zip ys) -> List.Mem (x, y') (xs.zip ys) -> y = y'
  | [], _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, _, h, _ => by cases h
  | a :: xs, b :: ys, x, y, y', hn, h1, h2 => by
    simp only [List.zip_cons_cons] at h1 h2
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

theorem uniqList_mem {M : Method} : forall {Ms : List Method}, List.Mem M Ms -> Method.uniqList Ms -> M.uniq
  | [], h, _ => by cases h
  | M' :: Ms, h, hu => by
    simp only [Method.uniqList] at hu
    cases h with
    | head => exact hu.1
    | tail _ h => exact uniqList_mem h hu.2

theorem vbindersListM_mem {M : Method} {x : VarName} : forall {Ms : List Method}, List.Mem M Ms ->
    List.Mem x M.vbinders -> List.Mem x (Method.vbindersList Ms)
  | [], h, _ => by cases h
  | M' :: Ms, h, hx => by
    simp only [Method.vbindersList, listMem_iff, List.mem_append]
    cases h with
    | head => exact Or.inl hx
    | tail _ h => exact Or.inr (vbindersListM_mem h hx)

theorem noShadowListM_mem' {M : Method} {Xs : List TVarName} {xs : List VarName} : forall {Ms : List Method},
    List.Mem M Ms -> Method.noShadowList Xs xs Ms = true -> M.noShadow Xs xs = true
  | [], h, _ => by cases h
  | M' :: Ms, h, hn => by
    simp only [Method.noShadowList, Bool.and_eq_true] at hn
    cases h with
    | head => exact hn.1
    | tail _ h => exact noShadowListM_mem' h hn.2

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
  cases h1 with
  | @simpleFieldFound D f Gs vs1 vs v hD hl hm =>
    cases h2 with
    | @simpleFieldFound D' f' Gs' vs1' vs' v' hD' hl' hm' =>
      simp only [Expr.field.injEq] at he
      have e1 := Value.expr_inj he.1
      simp only [Value.new.injEq] at e1
      have eD := dec_unique hwf hD.dec_mem hD'.dec_mem e1.1
      subst eD
      have ev := List.append_inj e1.2.2 (by rw [hl, hl'])
      rw [ev.1, he.2] at hm
      rw [zip_unique (fields_nodup hwf hD.dec_mem) hm hm']
      exact Fresh.refl _
    | @simpleFieldSuper D' f' Gs' vs1' vs' hD' hl' hn' hO' hG' =>
      simp only [Expr.field.injEq] at he
      have e1 := Value.expr_inj he.1
      simp only [Value.new.injEq] at e1
      have eD := dec_unique hwf hD.dec_mem hD'.dec_mem e1.1
      subst eD
      rw [he.2] at hm
      exact absurd (zip_mem_fst hm) hn'
    | innerFieldSuper => simp [Value.expr] at he
    | _ => simp at he
  | @simpleFieldSuper D f Gs vs1 vs hD hl hn hO hG =>
    cases h2 with
    | @simpleFieldFound D' f' Gs' vs1' vs' v' hD' hl' hm' =>
      simp only [Expr.field.injEq] at he
      have e1 := Value.expr_inj he.1
      simp only [Value.new.injEq] at e1
      have eD := dec_unique hwf hD.dec_mem hD'.dec_mem e1.1
      subst eD
      rw [<- he.2] at hm'
      exact absurd (zip_mem_fst hm') hn
    | @simpleFieldSuper D' f' Gs' vs1' vs' hD' hl' hn' hO' hG' =>
      simp only [Expr.field.injEq] at he
      have e1 := Value.expr_inj he.1
      simp only [Value.new.injEq] at e1
      have eD := dec_unique hwf hD.dec_mem hD'.dec_mem e1.1
      subst eD
      have ev := List.append_inj e1.2.2 (by rw [hl, hl'])
      rw [ev.2, he.2, e1.2.1]
      exact Fresh.refl _
    | innerFieldSuper => simp [Value.expr] at he
    | _ => simp at he
  | @innerFieldSuper C C' Ms f Gs Gs' vs =>
    cases h2 with
    | @innerFieldSuper C2 C2' Ms2 f2 Gs2 Gs2' vs2 =>
      simp only [Expr.field.injEq] at he
      have e1 := Value.expr_inj he.1
      simp only [Value.newLocal.injEq] at e1
      rw [e1.2.2.1, e1.2.2.2.1, e1.2.2.2.2.1, he.2]
      exact Fresh.refl _
    | simpleFieldFound => simp [Value.expr] at he
    | simpleFieldSuper => simp [Value.expr] at he
    | _ => simp at he
  | @ifThen C' Ts Ts' x e1 e1' e2 v hs hf hd =>
    cases h2 with
    | @ifThen C2 Ts2 Ts2' x2 e12 e12' e22 v2 hs2 hf2 hd2 =>
      simp only [Expr.ifInst.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [<- he.2.2.1] at hd2 hw2
      rw [<- he.2.2.2.1] at hf2
      rw [<- he.2.2.1]
      have hn := ha.2.2.2.2.1
      simp only [Expr.noShadow, Bool.and_eq_true] at hn
      have hu := ha.uniq
      simp only [Expr.uniq] at hu
      have ht := ha.noThis
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht
      have hc := ha.2.2.2.2.2.2
      simp only [Expr.closed, Bool.and_eq_true] at hc
      exact fresh_if hf hf2 hd hd2 hw1 hw2 hn.1.2 hu.2.1 ht.1.2 hc.1.1.1
    | @ifElse C2 Ts2 x2 e12 e22 v2 hn2 =>
      simp only [Expr.ifInst.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      simp only [Ty.cls.injEq] at he
      rw [<- he.2.1.1] at hn2
      exact absurd (Exists.intro Ts' hs) hn2
    | _ => simp at he
  | @ifElse C' Ts x e1 e2 v hn =>
    cases h2 with
    | @ifThen C2 Ts2 Ts2' x2 e12 e12' e22 v2 hs2 hf2 hd2 =>
      simp only [Expr.ifInst.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      simp only [Ty.cls.injEq] at he
      rw [he.2.1.1] at hn
      exact absurd (Exists.intro Ts2' hs2) hn
    | @ifElse C2 Ts2 x2 e12 e22 v2 hn2 =>
      simp only [Expr.ifInst.injEq] at he
      rw [he.2.2.2.2]
      exact Fresh.refl _
    | _ => simp at he
  | @simpleAddSuper C m v Gs Gs' vs0 vs hv =>
    cases h2 with
    | @simpleAddSuper C2 m2 v2 Gs2 Gs2' vs02 vs2 hv2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [hv] at hv2
      simp only [Value.new.injEq] at hv2
      rw [hv2.1, hv2.2.1, GTy.tys_inj he.2.1, he.2.2.1, Value.exprs_inj he.2.2.2]
      exact Fresh.refl _
    | @innerFound C2 C2' Ms2 M2 m2 D2 T2 ps2 e02 e2 v02 Gs2 Gs2'' Gs2' vs02 vs2 hv2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [hv] at hv2
      simp at hv2
    | @innerSuper C2 C2' Ms2 m2 v02 Gs20 Gs2 Gs2' vs02 vs2 hv2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [hv] at hv2
      simp at hv2
    | _ => simp at he
  | @innerFound C C' Ms M m Delta' T0 ps e0 e v0 Gs Gs'' Gs' vs0 vs hv hM hF hG hp hN hN' hgs hvs hres =>
    cases h2 with
    | @simpleAddSuper C2 m2 v2 Gs2 Gs2' vs02 vs2 hv2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [hv] at hv2
      simp at hv2
    | @innerFound C2 C2' Ms2 M2 m2 D2 T2 ps2 e02 e2 v02 Gs2 Gs2'' Gs2' vs02 vs2 hv2 hM2 hF2 hG2 hp2 hN2 hN2' hgs2 hvs2 hres2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      have eG := GTy.tys_inj he.2.1
      have evs := Value.exprs_inj he.2.2.2
      subst eG evs
      rw [hv] at hv2
      simp only [Value.newLocal.injEq] at hv2
      rw [<- hv2.2.2.2.2.2] at hM2
      rw [<- he.2.2.1] at hF2
      subst hv hres hres2
      have hloc := ha.1 (K.loc C (Gs.map Funnel.ground) C' (GTy.tys Gs'') (Value.exprs vs0) Ms)
        (List.mem_append_left _ (List.Mem.head _))
      have eM : M = M2 := nodup_map_inj hloc hM hM2 (by rw [FreshM.name hF, FreshM.name hF2])
      subst eM
      have hu := ha.uniq
      simp only [Expr.uniq, Value.expr] at hu
      have hMu := uniqList_mem hM hu.1.2
      have ht := ha.noThis
      simp only [NoThis, Expr.vbinders, Value.expr, listMem_iff, List.mem_append, not_or] at ht
      have hMt : NoThisM M := fun h => ht.1.2 (vbindersListM_mem hM h)
      have hn := ha.2.2.2.2.1
      simp only [Expr.noShadow, Value.expr, Bool.and_eq_true] at hn
      have hMn : Method.noShadow (dom []) [] M = true := noShadowListM_mem' hM hn.1.2
      have hc := ha.2.2.2.2.2.2
      simp only [Expr.closed, Bool.and_eq_true] at hc
      have hvals := closed_cons_vals hc.1.1 hc.2
      exact And.intro
        (renE_meth (B := []) (Gs := []) hF.2 hF2.1 hMu hMt hMn rfl hG hG2 hp hp2 hN hN2 hN' hN2' hgs hgs2 hvs hvs2
          hw1.2.2.2.2.2.2 hvals)
        (renE_meth (B := []) (Gs := []) hF2.2 hF.1 hMu hMt hMn rfl hG2 hG hp2 hp hN2 hN hN2' hN' hgs2 hgs hvs2 hvs
          hw2.2.2.2.2.2.2 hvals)    | @innerSuper C2 C2' Ms2 m2 v02 Gs20 Gs2 Gs2' vs02 vs2 hv2 hm2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [hv] at hv2
      simp only [Value.newLocal.injEq] at hv2
      rw [<- hv2.2.2.2.2.2, <- he.2.2.1] at hm2
      exact absurd (by rw [<- FreshM.name hF]; exact List.mem_map_of_mem hM) hm2
    | _ => simp at he
  | @innerSuper C C' Ms m v0 Gs0 Gs Gs' vs0 vs hv hm =>
    cases h2 with
    | @simpleAddSuper C2 m2 v2 Gs2 Gs2' vs02 vs2 hv2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [hv] at hv2
      simp at hv2
    | @innerFound C2 C2' Ms2 M2 m2 D2 T2 ps2 e02 e2 v02 Gs2 Gs2'' Gs2' vs02 vs2 hv2 hM2 hF2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [hv] at hv2
      simp only [Value.newLocal.injEq] at hv2
      rw [<- hv2.2.2.2.2.2] at hM2
      rw [he.2.2.1] at hm
      exact absurd (by rw [<- FreshM.name hF2]; exact List.mem_map_of_mem hM2) hm
    | @innerSuper C2 C2' Ms2 m2 v02 Gs20 Gs2 Gs2' vs02 vs2 hv2 hm2 =>
      simp only [Expr.call.injEq] at he
      have ev := Value.expr_inj he.1
      subst ev
      rw [hv] at hv2
      simp only [Value.newLocal.injEq] at hv2
      rw [hv2.2.2.1, hv2.2.2.2.1, GTy.tys_inj he.2.1, he.2.2.1, Value.exprs_inj he.2.2.2]
      exact Fresh.refl _
    | _ => simp at he
  | @simpleFound D M m Delta' T0 ps e0 e v0 Gs Gs' vs hD hM hF hG hG' hN hN' hp hgs hvs hres =>
    cases h2 with
    | @simpleFound D2 M2 m2 D2' T2 ps2 e02 e2 v02 Gs2 Gs2' vs2 hD2 hM2 hF2 hG2 hG2' hN2 hN2' hp2 hgs2 hvs2 hres2 =>
      simp only [Expr.superCall.injEq, Ty.cls.injEq] at he
      have eD := dec_unique hwf hD.dec_mem hD2.dec_mem he.2.1.1
      subst eD
      have ev := Value.expr_inj he.1
      have eG := GTy.tys_inj he.2.1.2
      have eG' := GTy.tys_inj he.2.2.1
      have evs := Value.exprs_inj he.2.2.2.2
      subst ev eG eG' evs hres hres2
      rw [<- he.2.2.2.1] at hF2
      have hA3 := hwf.2.2.1 (K.dec D) (classes_mem_dec hD.dec_mem)
      have eM : M = M2 := nodup_map_inj hA3 hM hM2 (by rw [FreshM.name hF, FreshM.name hF2])
      subst eM
      have hMf := hwf.method hD.dec_mem hM
      have hc := ha.2.2.2.2.2.2
      simp only [Expr.closed, Bool.and_eq_true] at hc
      have hvals := closed_cons_vals hc.1.1 hc.2
      exact And.intro
        (renE_meth hF.2 hF2.1 hMf.1 hMf.2.1 hMf.2.2 hG hG' hG2' hp hp2 hN hN2 hN' hN2' hgs hgs2 hvs hvs2
          hw1.2.2.2.2.2.2 hvals)
        (renE_meth hF2.2 hF.1 hMf.1 hMf.2.1 hMf.2.2 hG hG2' hG' hp2 hp hN2 hN hN2' hN' hgs2 hgs hvs2 hvs
          hw2.2.2.2.2.2.2 hvals)
    | @searchSuper D2 m2 v2 Gs2 Gs2' vs2 hD2 hm2 hO2 hG2 =>
      simp only [Expr.superCall.injEq, Ty.cls.injEq] at he
      have eD := dec_unique hwf hD.dec_mem hD2.dec_mem he.2.1.1
      subst eD
      rw [<- he.2.2.2.1] at hm2
      exact absurd (by rw [<- FreshM.name hF]; exact List.mem_map_of_mem hM) hm2
    | _ => simp at he
  | @searchSuper D m v Gs Gs' vs hD hm hO hG =>
    cases h2 with
    | @simpleFound D2 M2 m2 D2' T2 ps2 e02 e2 v02 Gs2 Gs2' vs2 hD2 hM2 hF2 =>
      simp only [Expr.superCall.injEq, Ty.cls.injEq] at he
      have eD := dec_unique hwf hD.dec_mem hD2.dec_mem he.2.1.1
      subst eD
      rw [he.2.2.2.1] at hm
      exact absurd (by rw [<- FreshM.name hF2]; exact List.mem_map_of_mem hM2) hm
    | @searchSuper D2 m2 v2 Gs2 Gs2' vs2 hD2 hm2 hO2 hG2 =>
      simp only [Expr.superCall.injEq, Ty.cls.injEq] at he
      have eD := dec_unique hwf hD.dec_mem hD2.dec_mem he.2.1.1
      subst eD
      rw [Value.expr_inj he.1, GTy.tys_inj he.2.1.2, GTy.tys_inj he.2.2.1, he.2.2.2.1, Value.exprs_inj he.2.2.2.2]
      exact Fresh.refl _
    | _ => simp at he

theorem determinismHigh {d : Decls} {e e1 e2 : Expr} (hwf : WFDecls d) (he : WFExpr e) (h1 : Reduces d e e1)
    (h2 : Reduces d e e2) : Fresh e1 e2 := by
  cases Step.toBase h1.1 with
  | intro E h =>
    cases h with
    | intro a h =>
      cases h with
      | intro a' h =>
        have hb := h.2.2
        have hna : NonValue a := Step.not_value hb.toStep
        have h2s := h2.1
        rw [h.1] at h2s he
        cases Step.decomp h2s hna with
        | intro a2 h3 =>
          have hb2 := Step.strip h3.1 hb
          have hw1 : WFExpr a' := by have := h1.2; rw [h.2.1] at this; exact WFExpr.plug this
          have hw2 : WFExpr a2 := by have := h2.2; rw [h3.2] at this; exact WFExpr.plug this
          rw [h.2.1, h3.2]
          exact Fresh.plug (det_base hwf (WFExpr.plug he) hw1 hw2 hb hb2 rfl) E

end Funnelling.High
