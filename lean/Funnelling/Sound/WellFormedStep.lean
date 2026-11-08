import Funnelling.Sound.FreshNames

open Funnelling.SoundSimp

namespace Funnelling

theorem localsList_eq : forall (es : List Expr), Expr.localsList es = es.flatMap Expr.locals
  | [] => rfl
  | e :: es => by simp [Expr.localsList, localsList_eq es]

theorem ifVarsList_eq : forall (es : List Expr), Expr.ifVarsList es = es.flatMap Expr.ifVars
  | [] => rfl
  | e :: es => by simp [Expr.ifVarsList, ifVarsList_eq es]

theorem noShadowList_eq {Xs : List TVarName} {xs : List VarName} :
    forall (es : List Expr), Expr.noShadowList Xs xs es = es.all (Expr.noShadow Xs xs)
  | [] => rfl
  | e :: es => by simp [Expr.noShadowList, noShadowList_eq es]

theorem closedList_eq {Xs : List TVarName} {xs : List VarName} :
    forall (es : List Expr), Expr.closedList Xs xs es = es.all (Expr.closed Xs xs)
  | [] => rfl
  | e :: es => by simp [Expr.closedList, closedList_eq es]

theorem ECtx.nodup_replace {a a' : Expr} (h' : forall k, List.Mem k a'.locals -> K.Nodup k) :
    forall (E : ECtx), (forall k, List.Mem k (E.plug a).locals -> K.Nodup k) ->
      forall k, List.Mem k (E.plug a').locals -> K.Nodup k := by
  intro E
  induction E <;> intro h
  case hole => exact h'
  all_goals
    rename_i ih
    simp only [ECtx.plug, Expr.locals, localsList_eq, List.flatMap_append, List.flatMap_cons, listMem_iff,
      List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq, K.Nodup] at h ih |-
    simp_all only [implies_true, and_self, K.Ms, K.Fs]

theorem ECtx.ifVars_replace {a a' : Expr} {x : VarName} (h' : Not (List.Mem x a'.ifVars)) :
    forall (E : ECtx), Not (List.Mem x (E.plug a).ifVars) -> Not (List.Mem x (E.plug a').ifVars) := by
  intro E
  induction E <;> intro h
  case hole => exact h'
  all_goals
    rename_i ih
    simp only [ECtx.plug, Expr.ifVars, ifVarsList_eq, List.flatMap_append, List.flatMap_cons, listMem_iff,
      List.mem_append, List.mem_cons, not_or] at h ih |-
    simp_all

theorem ECtx.noShadow_replace {a a' : Expr} {Xs : List TVarName} {xs : List VarName}
    (h' : a'.noShadow Xs xs = true) :
    forall (E : ECtx), (E.plug a).noShadow Xs xs = true -> (E.plug a').noShadow Xs xs = true := by
  intro E
  induction E <;> intro h
  case hole => exact h'
  all_goals
    rename_i ih
    simp only [ECtx.plug, Expr.noShadow, noShadowList_eq, List.all_append, List.all_cons, Bool.and_eq_true] at h ih |-
    simp_all

theorem ECtx.closed_replace {a a' : Expr} {Xs : List TVarName} {xs : List VarName}
    (h' : a'.closed Xs xs = true) :
    forall (E : ECtx), (E.plug a).closed Xs xs = true -> (E.plug a').closed Xs xs = true := by
  intro E
  induction E <;> intro h
  case hole => exact h'
  all_goals
    rename_i ih
    simp only [ECtx.plug, Expr.closed, closedList_eq, List.all_append, List.all_cons, Bool.and_eq_true] at h ih |-
    simp_all

theorem WFExpr.nodup {e : Expr} (h : WFExpr e) : forall k, List.Mem k e.locals -> K.Nodup k := by
  intro k hk
  have hm : forall M, List.Mem M k.Ms -> List.Mem M e.methods := fun M hM => by
    simp only [Expr.methods, listMem_iff, List.mem_flatMap]
    exact Exists.intro k (And.intro hk hM)
  refine And.intro (h.1 k hk) (And.intro (h.2.2.2.1 k hk) (fun M hM => And.intro (h.2.1 M (hm M hM))
    (And.intro (h.2.2.1 _ (List.mem_map_of_mem (f := Method.bounds) (hm M hM))) (h.2.2.2.2.2.1.1 M (hm M hM)))))

theorem WFExpr.of_nodup {e : Expr} (hk : forall k, List.Mem k e.locals -> K.Nodup k) (hn : e.noShadow [] [] = true)
    (hi : Not (List.Mem this e.ifVars)) (hc : e.closed [] [] = true) : WFExpr e := by
  have hm : forall M, List.Mem M e.methods -> exists k, List.Mem k e.locals /\ List.Mem M k.Ms := fun M hM => by
    simp only [Expr.methods, listMem_iff, List.mem_flatMap] at hM
    exact hM
  refine And.intro (fun k h => (hk k h).1) (And.intro ?_ (And.intro ?_ (And.intro (fun k h => (hk k h).2.1)
    (And.intro hn (And.intro (And.intro ?_ hi) hc)))))
  . intro M hM
    rcases hm M hM with ⟨k, h1, h2⟩
    exact ((hk k h1).2.2 M h2).1
  . intro D hD
    simp only [listMem_iff, List.mem_map] at hD
    rcases hD with ⟨M, hM, e⟩
    subst e
    rcases hm M hM with ⟨k, h1, h2⟩
    exact ((hk k h1).2.2 M h2).2.1
  . intro M hM
    rcases hm M hM with ⟨k, h1, h2⟩
    exact ((hk k h1).2.2 M h2).2.2

theorem WFExpr.replace {E : ECtx} {a a' : Expr} (h : WFExpr (E.plug a)) (h' : WFExpr a') :
    WFExpr (E.plug a') :=
  WFExpr.of_nodup (ECtx.nodup_replace h'.nodup E h.nodup) (ECtx.noShadow_replace h'.2.2.2.2.1 E h.2.2.2.2.1)
    (ECtx.ifVars_replace h'.2.2.2.2.2.1.2 E h.2.2.2.2.2.1.2)
    (ECtx.closed_replace h'.2.2.2.2.2.2 E h.2.2.2.2.2.2)

theorem super_ground {d : Decls} (hok : DeclsOk d) {D : Dec} (hD : Declared d (.dec D)) {Gs : List GTy}
    (hl : Gs.length = D.bounds.length) :
    Ty.ftvList (Ty.substList (bind D.bounds (GTy.tys Gs)) D.Ts) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro X hX
  rw [<- gsubst_ty_bind] at hX
  have h := Ty.ftvList_gsubst hX
  apply h.2
  rw [bind_fst hl]
  exact Kind.ftv ((hok D hD.dec_mem).2.1 _ (List.Mem.head _)) X h.1

theorem wf_field {e : Expr} {f : FieldName} : WFExpr (.field e f) <-> WFExpr e := Iff.rfl

theorem wf_new_mem {C : ClassName} {Ts : List Ty} {es : List Expr} {e : Expr} (h : WFExpr (.new C Ts es))
    (he : List.Mem e es) : WFExpr e := by
  have hn := h.2.2.2.2.1
  have hc := h.2.2.2.2.2.2
  simp only [Expr.noShadow, Expr.closed, Bool.and_eq_true] at hn hc
  exact WFExpr.sub h (fun _ hk => Expr.mem_localsList he hk) (fun _ hx => Expr.mem_ifVarsList he hx)
    (Expr.noShadowList_mem he hn) (Expr.closedList_mem he hc.2)

theorem wf_new_suffix {C C' : ClassName} {Ts Ts' : List Ty} {l r : List Expr} (h : WFExpr (.new C Ts (l ++ r)))
    (hT : Ty.ftvList Ts' = []) : WFExpr (.new C' Ts' r) := by
  have hn := h.2.2.2.2.1
  have hc := h.2.2.2.2.2.2
  simp only [Expr.noShadow, noShadowList_eq, List.all_append, Bool.and_eq_true, Expr.closed, closedList_eq] at hn hc
  refine WFExpr.sub h ?_ ?_ ?_ ?_
  . intro k hk
    simp only [Expr.locals, localsList_eq, List.flatMap_append, listMem_iff, List.mem_append] at hk |-
    exact Or.inr hk
  . intro x hx
    simp only [Expr.ifVars, ifVarsList_eq, List.flatMap_append, listMem_iff, List.mem_append] at hx |-
    exact Or.inr hx
  . simp only [Expr.noShadow, noShadowList_eq]; exact hn.2
  . simp only [Expr.closed, closedList_eq, hT, List.all_nil, Bool.true_and]; exact hc.2.2

theorem wf_local_new {C C' : ClassName} {Fs : List Funnel} {Ts : List Ty} {es : List Expr} {Ms : List Method}
    (h : WFExpr (.newLocal C Fs C' Ts es Ms)) : WFExpr (.new C' Ts es) := by
  have hn := h.2.2.2.2.1
  have hc := h.2.2.2.2.2.2
  simp only [Expr.noShadow, Bool.and_eq_true, Expr.closed, List.all_append] at hn hc
  refine WFExpr.sub h ?_ ?_ ?_ ?_
  . intro k hk; simp only [Expr.locals, listMem_iff, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hk)
  . intro x hx; simp only [Expr.ifVars, listMem_iff, List.mem_append]; exact Or.inl hx
  . exact hn.1
  . simp only [Expr.closed, Bool.and_eq_true]; exact ⟨hc.1.1.2, hc.1.2⟩

theorem wf_if_else {e0 : Expr} {T : Ty} {x : VarName} {e1 e2 : Expr} (h : WFExpr (.ifInst e0 T x e1 e2)) :
    WFExpr e2 := by
  have hn := h.2.2.2.2.1
  have hc := h.2.2.2.2.2.2
  simp only [Expr.noShadow, Bool.and_eq_true, Expr.closed] at hn hc
  refine WFExpr.sub h ?_ ?_ hn.2 hc.2
  . intro k hk; simp only [Expr.locals, listMem_iff, List.mem_append, or_assoc]; exact Or.inr (Or.inr hk)
  . intro y hy; simp only [Expr.ifVars, listMem_iff, List.mem_cons, List.mem_append, or_assoc]; exact Or.inr (Or.inr (Or.inr hy))

theorem wf_call_super {e : Expr} {T : Ty} {Ts : List Ty} {m : MethName} {es : List Expr}
    (h : WFExpr (.call e Ts m es)) (hT : T.ftv = []) : WFExpr (.superCall e T Ts m es) := by
  have hc := h.2.2.2.2.2.2
  refine WFExpr.sub h (fun _ hk => hk) (fun _ hx => hx) h.2.2.2.2.1 ?_
  simp only [Expr.closed, Ty.ftvList, hT, List.nil_append] at hc |-
  exact hc

theorem wf_super_retype {e : Expr} {T T' : Ty} {Ts : List Ty} {m : MethName} {es : List Expr}
    (h : WFExpr (.superCall e T Ts m es)) (hT : T'.ftv = []) : WFExpr (.superCall e T' Ts m es) := by
  have hc := h.2.2.2.2.2.2
  refine WFExpr.sub h (fun _ hk => hk) (fun _ hx => hx) h.2.2.2.2.1 ?_
  simp only [Expr.closed, Ty.ftvList, hT, List.nil_append, List.all_append, Bool.and_eq_true] at hc |-
  exact ⟨⟨hc.1.1, hc.1.2.2⟩, hc.2⟩

theorem RenM.lens {rv : VRen} {rt : TRen} {M M' : Method} (h : RenM rv rt M M') :
    M'.bounds.length = M.bounds.length /\ M'.params.length = M.params.length /\ M'.name = M.name := by
  cases h with
  | mk h1 h2 _ => simp [Method.bounds, Method.params, Method.name, h1, h2]

theorem wf_vsubst {e : Expr} {n : VSubst} (hk : forall k, List.Mem k e.locals -> K.Nodup k)
    (hn : e.noShadow [] [] = true) (hi : Not (List.Mem this e.ifVars)) (hc : e.closed [] (n.map Prod.fst) = true)
    (hv : forall p, List.Mem p n -> WFExpr p.2.expr)
    (hd : forall p, List.Mem p n -> (forall y, List.Mem y p.2.expr.vbinders -> Not (List.Mem y e.vbinders)) /\
      (forall X, List.Mem X p.2.expr.tbinders -> Not (List.Mem X e.tbinders))) :
    WFExpr (e.vsubst n) := by
  have hthis : Not (List.Mem this (n.flatMap fun p => p.2.expr.vbinders)) := by
    intro h
    simp only [listMem_iff, List.mem_flatMap] at h
    rcases h with ⟨p, hp, h⟩
    exact WFExpr.noThis (hv p hp) h
  have hvns : VNS n (n.flatMap fun p => p.2.expr.vbinders) (n.flatMap fun p => p.2.expr.tbinders) := by
    intro p hp
    refine ⟨(hv p hp).2.2.2.2.1, fun y hy => ?_, fun X hX => ?_⟩
    . simp only [listMem_iff, List.mem_flatMap]; exact ⟨p, hp, hy⟩
    . simp only [listMem_iff, List.mem_flatMap]; exact ⟨p, hp, hX⟩
  refine WFExpr.of_nodup (Expr.nodup_vsubst hk (fun p hp => (hv p hp).nodup)) ?_
    (Expr.ifVars_vsubst hi (fun p hp => (hv p hp).2.2.2.2.2.1.2))
    (Expr.closed_vsubst (S := []) hc (fun p hp => (hv p hp).2.2.2.2.2.2))
  refine Expr.noShadow_vsubst hthis hn hvns (fun y hy => by cases hy) ?_ (fun X hX => by cases hX) ?_
  . intro y hy h
    simp only [listMem_iff, List.mem_flatMap] at h
    rcases h with ⟨p, hp, h⟩
    exact (hd p hp).1 y h hy
  . intro X hX h
    simp only [listMem_iff, List.mem_flatMap] at h
    rcases h with ⟨p, hp, h⟩
    exact (hd p hp).2 X h hX

theorem wf_ifThen {C' : ClassName} {Ts : List Ty} {x : VarName} {e1 e2 : Expr} {v : Value}
    (ha : WFExpr (.ifInst v.expr (.cls C' Ts) x e1 e2)) :
    exists e1', Fresh e1 e1' /\ VSubstDefined [x] e1' /\ WFExpr (e1'.vsubst [(x, v)]) := by
  have hk := ha.nodup
  have hn := ha.2.2.2.2.1
  have hc := ha.2.2.2.2.2.2
  have ht := WFExpr.noThis ha
  simp only [Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and, Expr.noShadow, Bool.and_eq_true,
    Expr.closed, NoThis, Expr.vbinders, List.mem_cons, not_or] at hk hn hc ht
  have hv : WFExpr v.expr := by
    refine WFExpr.sub ha ?_ ?_ hn.1.1.1 hc.1.1.1
    . intro k hk'; simp only [Expr.locals, listMem_iff, List.mem_append]; exact Or.inl (Or.inl hk')
    . intro y hy; simp only [Expr.ifVars, listMem_iff, List.mem_append, List.mem_cons]; exact Or.inl (Or.inl (Or.inr hy))
  rcases fresh_avoid e1 (v.expr.vbinders ++ [x]) v.expr.tbinders hk.1.2 hc.1.2 ht.1.2 with
    ⟨e1', hf, hav, hat, hk', hn', hi', hc'⟩
  refine ⟨e1', hf, fun y hy hm => hav y hy (List.mem_append_right _ hm), ?_⟩
  refine wf_vsubst hk' (Expr.noShadow_mono hn' (fun _ _ hX => hX) (fun y _ hy => by cases hy)) hi' hc' ?_ ?_
  . intro p hp
    cases hp with
    | head => exact hv
    | tail _ h => cases h
  . intro p hp
    cases hp with
    | head => exact ⟨fun y hy hm => hav y hm (List.mem_append_left _ hy), fun X hX hm => hat X hm hX⟩
    | tail _ h => cases h

theorem wf_call_arg {e0 : Expr} {Ts : List Ty} {m : MethName} {es : List Expr} {e : Expr}
    (h : WFExpr (.call e0 Ts m es)) (he : List.Mem e es) : WFExpr e := by
  have hn := h.2.2.2.2.1
  have hc := h.2.2.2.2.2.2
  simp only [Expr.noShadow, Bool.and_eq_true, Expr.closed] at hn hc
  exact WFExpr.sub h (fun _ hk => List.mem_append_right _ (Expr.mem_localsList he hk))
    (fun _ hx => List.mem_append_right _ (Expr.mem_ifVarsList he hx)) (Expr.noShadowList_mem he hn.2) (Expr.closedList_mem he hc.2)

theorem wf_found {M : Method} {m : MethName} {B0 Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr}
    {v0 : Value} {Gs Gs' : List GTy} {vs : List Value} (hF : FreshM M (.mk Delta' T0 m ps e0))
    (hG : Gs.length = B0.length) (hG' : Gs'.length = Delta'.length) (hp : ps.length = vs.length)
    (hnD : (dom B0).Nodup) (hkM : forall k, List.Mem k M.locals -> K.Nodup k)
    (hcM : M.closed (dom B0) [] = true) (htM : NoThisM M) (hv0 : WFExpr v0.expr)
    (hvs : forall v, List.Mem v vs -> WFExpr v.expr) :
    exists Delta2 T2 ps2 e2, Found M B0 Delta2 T2 m ps2 e2 Gs Gs' v0 vs := by
  rcases freshM_avoid M (v0.expr.vbinders ++ Expr.vbindersList (Value.exprs vs))
    (v0.expr.tbinders ++ Expr.tbindersList (Value.exprs vs)) hkM hcM htM with
    ⟨M', hF', hav, hat, hk', hn', hi', hc', ht', hu'⟩
  cases M' with
  | mk Delta2 T2 m' ps2 e2 =>
  have hl := RenM.lens hF'.1
  have hl0 := RenM.lens hF.1
  have hm' : m' = m := hl.2.2.trans hl0.2.2.symm
  subst hm'
  have hb : Delta2.length = Delta'.length := hl.1.trans hl0.1.symm
  have hq : ps2.length = ps.length := hl.2.1.trans hl0.2.1.symm
  simp only [Method.noShadow, Bool.and_eq_true, List.nil_append, List.cons_append] at hn'
  simp only [Method.closed, Bool.and_eq_true, List.nil_append, List.cons_append] at hc'
  simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ht'
  simp only [Method.vbinders, listMem_iff, List.mem_append] at hav
  simp only [Method.tbinders, listMem_iff, List.mem_append] at hat
  have hlen : Gs'.length = Delta2.length := by omega
  have hp' : ps2.length = vs.length := by omega
  have hN : (dom B0 ++ dom Delta2).Nodup := by
    apply List.nodup_append.mpr
    refine And.intro hnD (And.intro hu'.1 ?_)
    intro a ha b hb e
    subst e
    exact not_mem_of_all_not_contains hn'.1.1 hb ha
  refine ⟨Delta2, T2, ps2, e2, hF', hlen, hp', hN, List.nodup_cons.mpr ⟨ht'.1, hu'.2.1⟩,
    fun X hX => Expr.noShadow_tb hn'.2 X hX, fun y hy => Expr.noShadow_binders hn'.2 ht'.2 y hy, ?_⟩
  have hz : ((this :: ps2.map VarDecl.x).zip (v0 :: vs)).map Prod.fst = this :: ps2.map VarDecl.x :=
    zip_map_fst (by simp [hp'])
  have hfst : (bind (B0 ++ Delta2) (Gs ++ Gs')).map Prod.fst = dom B0 ++ dom Delta2 := by
    rw [bind_fst (by simp [hG, hlen])]; exact dom_append
  refine wf_vsubst (Expr.nodup_gsubst hk') ?_ ?_ ?_ ?_ ?_
  . rw [Expr.noShadow_gsubst]
    exact Expr.noShadow_mono hn'.2 (fun X _ h => by cases h) (fun y _ h => by cases h)
  . rw [Expr.ifVars_gsubst]; exact hi'
  . rw [hz]; exact Expr.closed_gsubst (T := []) (by rw [List.nil_append, hfst]; exact hc'.2)
  . intro p hp
    rcases p with ⟨px, pv⟩
    cases (List.of_mem_zip hp).2 with
    | head => exact hv0
    | tail _ h => exact hvs pv h
  . intro p hp
    rcases p with ⟨px, pv⟩
    have hpv := (List.of_mem_zip hp).2
    refine ⟨fun y hy hm => ?_, fun X hX hm => ?_⟩
    . rw [Expr.vbinders_gsubst] at hm
      apply hav y (Or.inr hm)
      cases hpv with
      | head => exact Or.inl hy
      | tail _ h => exact Or.inr (Expr.mem_vbindersList (Value.mem_exprs h) hy)
    . rw [Expr.tbinders_gsubst] at hm
      apply hat X (Or.inr hm)
      cases hpv with
      | head => exact Or.inl hX
      | tail _ h => exact Or.inr (Expr.mem_tbindersList (Value.mem_exprs h) hX)

theorem wf_innerFound {C C' : ClassName} {Ms : List Method} {M : Method} {m : MethName} {Delta' : Bounds} {T0 : Ty}
    {ps : List VarDecl} {e0 : Expr} {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} (hM : List.Mem M Ms)
    (hF : FreshM M (.mk Delta' T0 m ps e0)) (hG' : Gs'.length = Delta'.length) (hp : ps.length = vs.length)
    (ha : WFExpr (.call (Value.newLocal C Gs C' Gs'' vs0 Ms).expr (GTy.tys Gs') m (Value.exprs vs))) :
    exists Delta2 T2 ps2 e2, Found M [] Delta2 T2 m ps2 e2 [] Gs' (Value.newLocal C Gs C' Gs'' vs0 Ms) vs := by
  have hv0 : WFExpr (Value.newLocal C Gs C' Gs'' vs0 Ms).expr :=
    WFExpr.plug (E := .callRecv .hole Gs' m (Value.exprs vs)) ha
  have hvs : forall v, List.Mem v vs -> WFExpr v.expr := fun v hv => wf_call_arg ha (Value.mem_exprs hv)
  have hk0 := hv0.nodup
  have hc0 := hv0.2.2.2.2.2.2
  have ht0 := WFExpr.noThis hv0
  simp only [Value.expr, Expr.locals, listMem_iff, List.mem_cons, List.mem_append, or_imp, forall_and,
    forall_eq] at hk0
  simp only [Value.expr, Expr.closed, Bool.and_eq_true] at hc0
  simp only [NoThis, Value.expr, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht0
  have hkM : forall k, List.Mem k M.locals -> K.Nodup k := fun k hk => hk0.2.2 k (Method.mem_localsList hM hk)
  have hcM : M.closed [] [] = true := Method.closedList_mem hM hc0.2
  have htM : NoThisM M := fun h => ht0.2 (Method.mem_vbindersList hM h)
  exact wf_found (B0 := []) (Gs := []) hF rfl hG' hp List.nodup_nil hkM hcM htM hv0 hvs

theorem WFDecls.nodup {d : Decls} (hwf : WFDecls d) : forall k, List.Mem k (classes d) -> K.Nodup k := by
  intro k hk
  have hl := hwf.locOk k hk
  exact And.intro (hwf.2.2.1 k hk) (And.intro (hwf.2.2.2.2.2.1 k hk)
    (fun M hM => And.intro (hl M hM).2.1 (And.intro (hl M hM).1 (hl M hM).2.2)))

theorem kinds_all {d : Decls} {Delta : Bounds} {Ts : List Ty} (h : forall T, List.Mem T Ts -> Kind d Delta T) :
    (Ty.ftvList Ts).all (dom Delta).contains = true := by
  apply all_contains_iff.mpr
  intro X hX
  rcases Ty.mem_ftvList.mp hX with ⟨T, hT, hX⟩
  exact Kind.ftv (h T hT) X hX

theorem Method.closed_this {M : Method} {T : List TVarName} {S : List VarName} (h : M.closed T (this :: S) = true) :
    M.closed T S = true := by
  cases M with
  | mk D T0 m ps e =>
    simp only [Method.closed, Bool.and_eq_true] at h |-
    refine ⟨h.1, Expr.closed_mono h.2 (fun _ h => h) ?_⟩
    intro y hy
    simp only [listMem_iff, List.mem_append, List.mem_cons] at hy |-
    rcases hy with (hy | hy | hy) | hy
    . exact Or.inl (Or.inl hy)
    . exact Or.inl (Or.inl hy)
    . exact Or.inl (Or.inr hy)
    . exact Or.inr hy

theorem closedListM_of {T : List TVarName} {S : List VarName} : forall {Ms : List Method},
    (forall M, List.Mem M Ms -> M.closed T S = true) -> Method.closedList T S Ms = true
  | [], _ => rfl
  | M :: Ms, h => by
    simp only [Method.closedList, Bool.and_eq_true]
    exact ⟨h M (List.Mem.head _), closedListM_of (fun M' hM' => h M' (List.Mem.tail _ hM'))⟩

mutual
theorem Typing.closed {d : Decls} : forall {Delta gamma e T}, Typing d Delta gamma e T ->
    e.closed (dom Delta) (gdom gamma) = true
  | _, _, _, _, .subs h _ _ => Typing.closed h
  | _, _, _, _, .var hl => List.contains_iff_mem.mpr (List.mem_map_of_mem (f := VarDecl.x) (lookup_mem_g hl))
  | _, _, _, _, .newObject => rfl
  | _, _, _, _, .declField h1 _ _ _ => by
    simp only [Expr.closed]
    exact Typing.closed h1
  | _, _, _, _, .call h1 _ _ _ _ _ h7 _ h9 => by
    simp only [Expr.closed, Bool.and_eq_true]
    exact ⟨⟨Typing.closed h1, kinds_all h7⟩, TypingSeq.closed h9⟩
  | _, _, _, _, .callLbRuntime _ _ _ _ _ _ _ h8 h9 _ h11 => by
    have hs := TypingSeq.closed h11
    simp only [Expr.closedList, Bool.and_eq_true] at hs
    simp only [Expr.closed, Bool.and_eq_true]
    refine ⟨⟨hs.1, kinds_all (d := d) ?_⟩, hs.2⟩
    intro T hT
    cases hT with
    | head => exact h8
    | tail _ hT => exact h9 T hT
  | _, _, _, _, .newTop _ h2 _ h4 h5 => by
    have h5c := Typing.closed h5
    simp only [Expr.closed, Bool.and_eq_true] at h5c
    simp only [Expr.closed, Bool.and_eq_true, closedList_eq, List.all_append]
    rw [closedList_eq] at h5c
    have h4c := TypingSeq.closed h4
    rw [closedList_eq] at h4c
    refine ⟨?_, h4c, h5c.2⟩
    apply all_contains_iff.mpr
    intro X hX
    exact Kind.ftv h2 X hX
  | _, _, _, _, .newLocal (Fs := Fs) _ h2 _ _ h5 h6 h7 _ => by
    have h6c := Typing.closed h6
    simp only [Expr.closed, Bool.and_eq_true] at h6c
    have hsD := Pairing.sub h2
    simp only [Expr.closed, Bool.and_eq_true, List.all_append]
    refine ⟨⟨⟨?_, ?_⟩, h6c.2⟩, closedListM_of (fun M hM => Method.closed_this
      (Method.closed_mono (MethodOk.closed (h7 M hM)) (dom_sub1 hsD) ?_))⟩
    . apply all_contains_iff.mpr
      intro X hX
      rw [<- Pairing.dom_eq h2] at hX
      exact dom_sub1 hsD X hX
    . simp_all
    . intro y hy
      simp only [gdom, withoutThis, restrict, List.map_append, listMem_iff, List.mem_append, List.mem_map,
        List.mem_filter, List.mem_singleton] at hy
      simp only [gdom, listMem_iff, List.mem_cons, List.mem_map]
      rcases hy with ⟨a, ha, e⟩ | ⟨a, ha, e⟩
      . exact Or.inr ⟨a, ha.1.1, e⟩
      . subst ha; exact Or.inl e.symm
  | _, _, _, _, .ifInstanceof h0 hk _ h1 h2 => by
    simp only [Expr.closed, Bool.and_eq_true]
    refine ⟨⟨⟨Typing.closed h0, ?_⟩, Expr.closed_mono (Typing.closed h1) (fun _ h => h) ?_⟩, Typing.closed h2⟩
    . apply all_contains_iff.mpr
      exact Kind.ftv hk
    . intro y hy
      rw [gdom_append_single] at hy
      simp only [listMem_iff, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy |-
      rcases hy with hy | hy
      . exact Or.inr hy
      . exact Or.inl hy
theorem TypingSeq.closed {d : Decls} : forall {Delta gamma es Ts}, TypingSeq d Delta gamma es Ts ->
    Expr.closedList (dom Delta) (gdom gamma) es = true
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons h hs => by
    simp only [Expr.closedList, Bool.and_eq_true]
    exact ⟨Typing.closed h, TypingSeq.closed hs⟩
theorem MethodOk.closed {d : Decls} : forall {Delta gamma M}, MethodOk d Delta gamma M ->
    M.closed (dom Delta) (gdom gamma) = true
  | _, _, _, .methodOk h1 h2 h3 => by
    simp only [Method.closed, Bool.and_eq_true]
    rw [<- dom_append]
    refine ⟨kinds_all (d := d) ?_, Expr.closed_mono (Typing.closed h3) (fun _ h => h) ?_⟩
    . intro T hT
      simp only [listMem_iff, List.mem_append, List.mem_cons] at hT
      rcases hT with (hT | hT) | hT
      . exact h2 T (by rw [hT]; exact List.Mem.head _)
      . exact h1 T hT
      . exact h2 T (List.Mem.tail _ hT)
    . intro y hy
      simp only [gdom, List.map_append, listMem_iff, List.mem_append, List.mem_cons] at hy |-
      rcases hy with hy | hy
      . exact Or.inl (Or.inr hy)
      . exact Or.inr hy
end

theorem dec_method_closed {d : Decls} (hok : DeclsOk d) {D : Dec} (hD : Declared d (.dec D))
    {M : Method} (hM : List.Mem M D.Ms) : M.closed (dom D.bounds) [] = true :=
  Method.closed_this (MethodOk.closed ((hok D hD.dec_mem).2.2.1 M hM))

theorem wf_super_arg {e0 : Expr} {T : Ty} {Ts : List Ty} {m : MethName} {es : List Expr} {e : Expr}
    (h : WFExpr (.superCall e0 T Ts m es)) (he : List.Mem e es) : WFExpr e := by
  have hn := h.2.2.2.2.1
  have hc := h.2.2.2.2.2.2
  simp only [Expr.noShadow, Bool.and_eq_true, Expr.closed] at hn hc
  exact WFExpr.sub h (fun _ hk => List.mem_append_right _ (Expr.mem_localsList he hk))
    (fun _ hx => List.mem_append_right _ (Expr.mem_ifVarsList he hx)) (Expr.noShadowList_mem he hn.2) (Expr.closedList_mem he hc.2)

theorem wf_simpleFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {D : Dec} {M : Method} {m : MethName}
    {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value} {Gs Gs' : List GTy} {vs : List Value}
    (hD : Declared d (.dec D)) (hM : List.Mem M D.Ms) (hF : FreshM M (.mk Delta' T0 m ps e0))
    (hG : Gs.length = D.bounds.length) (hG' : Gs'.length = Delta'.length) (hp : ps.length = vs.length)
    (ha : WFExpr (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs))) :
    exists Delta2 T2 ps2 e2, Found M D.bounds Delta2 T2 m ps2 e2 Gs Gs' v0 vs := by
  have hd := hD.dec_mem
  rcases WFDecls.method hwf hd hM with ⟨-, htM, -⟩
  have hkM : forall k, List.Mem k M.locals -> K.Nodup k :=
    fun k hk => WFDecls.nodup hwf k (classes_mem_loc hd (Method.mem_localsList hM hk))
  have hcM := dec_method_closed hok hD hM
  have hv0 : WFExpr v0.expr := WFExpr.plug (E := .superRecv .hole (GTy.cls D.C Gs) Gs' m (Value.exprs vs)) ha
  have hvs : forall v, List.Mem v vs -> WFExpr v.expr := fun v hv => wf_super_arg ha (Value.mem_exprs hv)
  exact wf_found hF hG hG' hp (hwf.2.2.2.2.1 D.bounds (by
    simp only [listMem_iff, List.mem_append, List.mem_map]
    exact Or.inl (Exists.intro D (And.intro hd rfl)))) hkM hcM htM hv0 hvs

theorem wf_base {d : Decls} {a a' : Expr} (hwf : WFDecls d) (hok : DeclsOk d) (ha : WFExpr a)
    (hs : BaseStep d a a') : exists a'', BaseStep d a a'' /\ WFExpr a'' := by
  cases hs with
  | simpleFieldFound h1 h2 h3 =>
    exact ⟨_, BaseStep.simpleFieldFound h1 h2 h3,
      wf_new_mem (wf_field.mp ha) (Value.mem_exprs (List.mem_append_left _ (List.of_mem_zip h3).2))⟩
  | simpleFieldSuper h1 h2 h3 h4 h5 =>
    refine ⟨_, BaseStep.simpleFieldSuper h1 h2 h3 h4 h5, ?_⟩
    have hw := wf_field.mp ha
    simp only [Value.expr, exprs_append] at hw
    exact wf_field.mpr (wf_new_suffix hw (super_ground hok h1 h5))
  | innerFieldSuper =>
    refine ⟨_, BaseStep.innerFieldSuper, ?_⟩
    have hw := wf_field.mp ha
    simp only [Value.expr] at hw |-
    exact wf_field.mpr (wf_local_new hw)
  | ifThen h1 _ _ =>
    rcases wf_ifThen ha with ⟨e1', hf, hd, hw⟩
    exact ⟨_, BaseStep.ifThen h1 hf hd, hw⟩
  | ifElse h1 => exact ⟨_, BaseStep.ifElse h1, wf_if_else ha⟩
  | simpleAddSuper h1 =>
    subst h1
    exact ⟨_, BaseStep.simpleAddSuper rfl, wf_call_super ha (by simp only [Ty.ftv]; exact GTy.ftv_tys _)⟩
  | simpleFound h1 h2 h3 h4 h5 _ _ h8 _ _ _ =>
    rcases wf_simpleFound hwf hok h1 h2 h3 h4 h5 h8 ha with ⟨_, _, _, _, f⟩
    exact ⟨_, BaseStep.simpleFound h1 h2 f.fresh h4 f.lenT f.nodupT f.nodupV f.lenV f.gdef f.vdef rfl, f.wf⟩
  | innerFound h1 h2 h3 h4 h5 _ _ _ _ _ =>
    subst h1
    rcases wf_innerFound h2 h3 h4 h5 ha with ⟨_, _, _, _, f⟩
    exact ⟨_, BaseStep.innerFound rfl h2 f.fresh f.lenT f.lenV f.nodupT f.nodupV f.gdef f.vdef rfl, f.wf⟩
  | innerSuper h1 h2 =>
    subst h1
    exact ⟨_, BaseStep.innerSuper rfl h2, wf_call_super ha (by simp only [Ty.ftv]; exact GTy.ftv_tys _)⟩
  | searchSuper h1 h2 h3 h4 =>
    exact ⟨_, BaseStep.searchSuper h1 h2 h3 h4,
      wf_super_retype ha (by simp only [Ty.ftv]; exact super_ground hok h1 h4)⟩

theorem wf_step {d : Decls} {e e' : Expr} (hwf : WFDecls d) (hok : DeclsOk d) (he : WFExpr e)
    (hs : Step d e e') : exists e'', Reduces d e e'' := by
  rcases Step.toBase hs with ⟨E, a, a', hE, _, hb⟩
  subst hE
  rcases wf_base hwf hok (WFExpr.plug he) hb with ⟨a'', hb'', hw''⟩
  exact ⟨E.plug a'', Step.ctx hb''.toStep, WFExpr.replace he hw''⟩

end Funnelling
