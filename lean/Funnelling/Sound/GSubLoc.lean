import Funnelling.Sound.RenOver

open Funnelling.SoundSimp

namespace Funnelling.High

abbrev GOk (d : Decls) (Delta : Bounds) (s : GSubst) : Prop :=
  forall b, List.Mem b Delta -> forall G, List.lookup b.X s = some G ->
    Sub d [] G.ty (b.T.subst s.ty) /\ Kind d [] G.ty /\ Kind d [] (b.T.subst s.ty)

abbrev gsubB (s : GSubst) (Delta : Bounds) : Bounds :=
  Bounds.subst s.ty (Delta.filter fun b => !((s.map Prod.fst).contains b.X))

abbrev gsubG (s : GSubst) (gamma : Gamma) : Gamma := gamma.map (VarDecl.subst s.ty)

theorem GOk.substCtx {d : Decls} {Delta : Bounds} {s : GSubst} (h : GOk d Delta s) :
    SubstCtx d Delta (gsubB s Delta) s.ty := by
  intro b hb
  cases hl : List.lookup b.X s with
  | none =>
    refine Or.inl (Exists.intro b.X (And.intro ?_ ?_))
    . simp only [Ty.subst, GSubst.lookup_ty, hl, Option.map_none, Option.getD_none]
    . simp only [gsubB, Bounds.subst, listMem_iff, List.mem_map, List.mem_filter]
      refine Exists.intro b (And.intro (And.intro hb ?_) rfl)
      have := lookup_none_not_dom' hl
      simpa using this
  | some G =>
    have hg := h b hb G hl
    have e : (Ty.var b.X).subst s.ty = G.ty := by
      simp only [Ty.subst, GSubst.lookup_ty, hl, Option.map_some, Option.getD_some]
    rw [e]
    have hG := hg.2.1
    cases G with
    | cls C Gs =>
      refine Or.inr (And.intro (Sub.cls_indep hg.1) (And.intro (Kind.mono (fun _ h => by cases h) hg.2.1)
        (Kind.mono (fun _ h => by cases h) hg.2.2)))
where
  lookup_none_not_dom' {X : TVarName} {s : GSubst} (h : List.lookup X s = none) : Not (List.Mem X (s.map Prod.fst)) := by
    intro hm
    rcases lookup_isSome hm with ⟨v, hv⟩; rw [hv] at h; cases h

theorem GOk.append {d : Decls} {Delta Dm : Bounds} {s : GSubst} (h : GOk d Delta s)
    (hm : forall b, List.Mem b Dm -> Not (List.Mem b.X (s.map Prod.fst))) : GOk d (Delta ++ Dm) s := by
  intro b hb G hl
  simp only [listMem_iff, List.mem_append] at hb
  rcases hb with hb | hb
  . exact h b hb G hl
  . exact absurd (lookup_some_mem_dom hl) (hm b hb)

theorem GOk.mono {d : Decls} {Delta Delta2 : Bounds} {s : GSubst} (h : GOk d Delta s) (hs : Sub1 Delta2 Delta) :
    GOk d Delta2 s := fun b hb => h b (hs b hb)

theorem gsubB_append {s : GSubst} {Delta Dm : Bounds}
    (hm : forall b, List.Mem b Dm -> Not (List.Mem b.X (s.map Prod.fst))) :
    gsubB s (Delta ++ Dm) = gsubB s Delta ++ Bounds.subst s.ty Dm := by
  simp only [gsubB, List.filter_append, Bounds.subst, List.map_append]
  congr 2
  apply List.filter_eq_self.mpr
  intro b hb
  simpa using hm b hb

theorem Gamma.lookup_gsubG {s : GSubst} {x : VarName} {T : Ty} : forall {gamma : Gamma}, gamma.lookup x = some T ->
    (gsubG s gamma).lookup x = some (T.subst s.ty)
  | [], h => by simp [Gamma.lookup] at h
  | y :: gamma, h => by
    by_cases hy : y.x = x
    . simp only [Gamma.lookup, List.find?_cons, hy, beq_self_eq_true, Option.map_some] at h |-
      simp only [gsubG, List.map_cons, List.find?_cons, VarDecl.subst, hy, beq_self_eq_true, Option.map_some]
      cases h
      rfl
    . have hb : (y.x == x) = false := by simpa using hy
      simp only [Gamma.lookup, List.find?_cons, hb] at h |-
      simp only [gsubG, List.map_cons, List.find?_cons, VarDecl.subst, hb]
      exact Gamma.lookup_gsubG (gamma := gamma) h

theorem gdom_gsubG {s : GSubst} {gamma : Gamma} : gdom (gsubG s gamma) = gdom gamma := by
  simp [gdom, gsubG, VarDecl.subst, List.map_map, Function.comp_def]

theorem Expr.gsubstList_append {s : GSubst} : forall {es1 es2 : List Expr},
    Expr.gsubstList s (es1 ++ es2) = Expr.gsubstList s es1 ++ Expr.gsubstList s es2
  | [], _ => rfl
  | e :: es1, es2 => by simp only [List.cons_append, Expr.gsubstList]; rw [Expr.gsubstList_append]

theorem tbindersList_append : forall {es1 es2 : List Expr},
    Expr.tbindersList (es1 ++ es2) = Expr.tbindersList es1 ++ Expr.tbindersList es2
  | [], _ => rfl
  | e :: es1, es2 => by simp only [List.cons_append, Expr.tbindersList]; rw [tbindersList_append, List.append_assoc]

theorem tbindersListM_mem {M : Method} {X : TVarName} : forall {Ms : List Method}, List.Mem M Ms ->
    List.Mem X M.tbinders -> List.Mem X (Method.tbindersList Ms)
  | [], h, _ => by cases h
  | M' :: Ms, h, hx => by
    simp only [Method.tbindersList, listMem_iff, List.mem_append]
    cases h with
    | head => exact Or.inl hx
    | tail _ h => exact Or.inr (tbindersListM_mem h hx)

theorem substList_app {s : TSubst} {Ts Us : List Ty} :
    Ty.substList s (Ts ++ Us) = Ty.substList s Ts ++ Ty.substList s Us := by
  simp [substList_eq_map]

theorem cod_subst {s : TSubst} {Dm : Bounds} : cod (Bounds.subst s Dm) = Ty.substList s (cod Dm) := by
  simp [cod, Bounds.subst, substList_eq_map, List.map_map, Function.comp_def]

theorem params_T_subst {s : TSubst} {ps : List VarDecl} :
    (ps.map (VarDecl.subst s)).map VarDecl.T = Ty.substList s (ps.map VarDecl.T) := by
  simp [VarDecl.subst, substList_eq_map, List.map_map, Function.comp_def]

theorem KindSeq.substC {d : Decls} (hd : DeclOk d) {Delta Delta' : Bounds} {s : TSubst} (hc : SubstCtx d Delta Delta' s)
    {Ts : List Ty} (h : KindSeq d Delta Ts) : KindSeq d Delta' (Ty.substList s Ts) := by
  intro T hT
  rw [substList_eq_map] at hT
  rcases List.mem_map.mp hT with ⟨U, hU⟩; rw [<- hU.2]; exact Kind.subst hd hc.sub hc.kind (h U hU.1)


theorem lookup_none_of_not_dom {X : TVarName} {s : GSubst} (h : Not (List.Mem X (s.map Prod.fst))) :
    List.lookup X s = none := by
  cases hl : List.lookup X s with
  | none => rfl
  | some G => exact absurd (lookup_some_mem_dom hl) h

theorem var_gsubst_none {X : TVarName} {s : GSubst} (h : Not (List.Mem X (s.map Prod.fst))) :
    (Ty.var X).subst s.ty = Ty.var X := by
  simp only [Ty.subst, GSubst.lookup_ty, lookup_none_of_not_dom h, Option.map_none, Option.getD_none]

theorem var_gsubst_some {X : TVarName} {s : GSubst} {G : GTy} (h : List.lookup X s = some G) :
    (Ty.var X).subst s.ty = G.ty := by
  simp only [Ty.subst, GSubst.lookup_ty, h, Option.map_some, Option.getD_some]

theorem abs_gsubst {s : GSubst} : forall {Fs : List Funnel}, abs (Fs.map (Funnel.gsubst s)) = Ty.substList s.ty (abs Fs)
  | [] => rfl
  | F :: Fs => by
    have ih := abs_gsubst (s := s) (Fs := Fs)
    simp only [abs, List.map_cons, Ty.substList] at ih |-
    rw [ih]
    congr 1
    cases F with
    | ground G => simp only [Funnel.gsubst, Funnel.abs]; exact (GTy.subst_ty G).symm
    | funnel X =>
      cases hl : List.lookup X s with
      | none => simp only [Funnel.gsubst, hl, Funnel.abs, Ty.subst, GSubst.lookup_ty, Option.map_none, Option.getD_none]
      | some G => simp only [Funnel.gsubst, hl, Funnel.abs]; exact (var_gsubst_some hl).symm

mutual
theorem Ty.ftv_gsubst {s : GSubst} {X : TVarName} : forall {T : Ty}, List.Mem X (T.subst s.ty).ftv ->
    List.Mem X T.ftv /\ Not (List.Mem X (s.map Prod.fst))
  | .var Y, h => by
    cases hl : List.lookup Y s with
    | none =>
      have hY : Not (List.Mem Y (s.map Prod.fst)) := fun hm => by
        cases lookup_isSome hm with | intro v hv => rw [hv] at hl; cases hl
      rw [var_gsubst_none hY] at h
      have e : X = Y := by simpa [Ty.ftv] using h
      subst e
      exact And.intro h hY
    | some G => rw [var_gsubst_some hl, GTy.ftv_ty] at h; cases h
  | .cls C Ts, h => by
    simp only [Ty.subst, Ty.ftv] at h |-
    exact Ty.ftvList_gsubst h
theorem Ty.ftvList_gsubst {s : GSubst} {X : TVarName} : forall {Ts : List Ty},
    List.Mem X (Ty.ftvList (Ty.substList s.ty Ts)) -> List.Mem X (Ty.ftvList Ts) /\ Not (List.Mem X (s.map Prod.fst))
  | [], h => by cases h
  | T :: Ts, h => by
    simp only [Ty.substList, Ty.ftvList, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . have := Ty.ftv_gsubst h; exact And.intro (Or.inl this.1) this.2
    . have := Ty.ftvList_gsubst h; exact And.intro (Or.inr this.1) this.2
end

mutual
theorem Ty.ftv_gsubst_back {s : GSubst} {X : TVarName} : forall {T : Ty}, List.Mem X T.ftv ->
    Not (List.Mem X (s.map Prod.fst)) -> List.Mem X (T.subst s.ty).ftv
  | .var Y, h, hX => by
    have e : X = Y := by simpa [Ty.ftv] using h
    subst e
    rw [var_gsubst_none hX]
    exact h
  | .cls C Ts, h, hX => by
    simp only [Ty.subst, Ty.ftv] at h |-
    exact Ty.ftvList_gsubst_back h hX
theorem Ty.ftvList_gsubst_back {s : GSubst} {X : TVarName} : forall {Ts : List Ty},
    List.Mem X (Ty.ftvList Ts) -> Not (List.Mem X (s.map Prod.fst)) -> List.Mem X (Ty.ftvList (Ty.substList s.ty Ts))
  | [], h, _ => by cases h
  | T :: Ts, h, hX => by
    simp only [Ty.substList, Ty.ftvList, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . exact Or.inl (Ty.ftv_gsubst_back h hX)
    . exact Or.inr (Ty.ftvList_gsubst_back h hX)
end

theorem substList_subst_gen {s s' : TSubst} {L : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (s.map Prod.fst)) :
    Ty.substList s' (Ty.substList s L) = Ty.substList (s.map fun p => (p.1, p.2.subst s')) L :=
  Ty.substList_comp (fun X hX => var_subst_comp_of_some (lookup_isSome (h X hX)))

theorem vars_gsubst {s : GSubst} {Xs : List TVarName} (h : forall X, List.Mem X Xs -> Not (List.Mem X (s.map Prod.fst))) :
    Ty.substList s.ty (vars Xs) = vars Xs := by
  apply Ty.substList_id
  intro X hX
  apply var_gsubst_none
  apply h
  rcases ftvList_mem.mp hX with ⟨T, hT⟩
  simp only [vars, listMem_iff, List.mem_map] at hT
  rcases hT.1 with ⟨Y, hY⟩; rw [<- hY.2] at hT; have := hT.2; simp [Ty.ftv] at this; rw [this]; exact hY.1

theorem Sub.cls_target {d : Decls} {Delta : Bounds} {T1 T : Ty} (h : Sub d Delta T1 T) :
    forall {C Ts}, T1 = .cls C Ts -> exists C' Ts', T = .cls C' Ts' := by
  induction h with
  | subRefl => intro C Ts e; exact Exists.intro C (Exists.intro Ts e)
  | subInherit _ _ _ ih => intro _ _ _; exact ih (C := _) (Ts := _) (by simp only [Ty.subst]; rfl)
  | subInheritLocal _ _ _ ih => intro _ _ _; exact ih (C := _) (Ts := _) (by simp only [Ty.subst]; rfl)
  | subVar _ _ _ => intro _ _ e; cases e

theorem gsubstList_mem {s : GSubst} {M' : Method} : forall {Ms : List Method}, List.Mem M' (Method.gsubstList s Ms) ->
    exists M, List.Mem M Ms /\ M' = M.gsubst s
  | [], h => by cases h
  | M :: Ms, h => by
    simp only [Method.gsubstList] at h
    cases h with
    | head => exact Exists.intro M (And.intro (List.Mem.head _) rfl)
    | tail _ h =>
      rcases gsubstList_mem h with ⟨M0, hM0⟩; exact Exists.intro M0 (And.intro (List.Mem.tail _ hM0.1) hM0.2)

theorem names_gsubst {s : GSubst} : forall {Ms : List Method}, (Method.gsubstList s Ms).map Method.name = Ms.map Method.name
  | [] => rfl
  | M :: Ms => by
    cases M with
    | mk Dm T0 m ps e => simp only [Method.gsubstList, Method.gsubst, List.map_cons, Method.name]; rw [names_gsubst]

theorem OverrideOkM.gsubst {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {s : GSubst} {C : ClassName}
    {Us : List Ty} {M : Method} (h : OverrideOkM d (.cls C Us) M)
    (hdis : forall X, List.Mem X (dom M.bounds) -> Not (List.Mem X (s.map Prod.fst))) :
    OverrideOkM d (.cls C (Ty.substList s.ty Us)) (M.gsubst s) := by
  cases M with
  | mk Dp T0p m psp ep =>
    simp only [Method.bounds] at hdis
    simp only [Method.gsubst]
    have hv := vars_gsubst hdis
    cases h with
    | absent h1 h2 => exact OverrideOkM.absent h1 h2
    | @dec D _ _ _ _ _ _ Do T0o pso eo h1 h2 h3 h4 h5 h6 =>
      have hcl := declMeth_closed hwf hok h1 h2
      simp only [K.gvars, <- dom_append] at hcl
      have hlen : (Us ++ vars (dom Dp)).length = (D.bounds ++ Do).length := by simp [h3, h4, vars, dom]
      refine OverrideOkM.dec h1 h2 (by rw [substList_length, h3])
        (by simp only [Bounds.subst, List.length_map]; exact h4) ?_ ?_
      . rw [dom_bounds_subst, cod_subst, <- h5, substList_bind_comp hlen hcl.1, substList_app, hv]
      . have e := congrArg (Ty.substList s.ty) h6
        rw [substList_bind_comp hlen hcl.2, substList_app, hv] at e
        rw [dom_bounds_subst, e, Ty.substList, params_T_subst]
    | @loc C Fs C0 Ts0 es Ms _ _ _ _ _ _ Do T0o pso eo h1 h2 h3 h4 h5 h6 =>
      have hcl := declMeth_closed hwf hok h1 h2
      simp only [K.gvars] at hcl
      have hfst : forall X, List.Mem X (domF Fs ++ dom Do) ->
          List.Mem X ((bindF Fs Us ++ bind Do (vars (dom Dp))).map Prod.fst) := by
        intro X hX
        simp only [listMem_iff, List.mem_append, List.map_append] at hX |-
        rcases hX with hX | hX
        . cases bindF_lookup_some h3 hX with
          | intro U hU => exact Or.inl (lookup_some_mem_dom hU)
        . exact Or.inr (by rw [bind_fst (by simp [h4, vars, dom])]; exact hX)
      refine OverrideOkM.loc h1 h2 (by rw [substList_length, h3])
        (by simp only [Bounds.subst, List.length_map]; exact h4) ?_ ?_
      . rw [dom_bounds_subst, cod_subst, <- h5, substList_subst_gen (fun X hX => hfst X (hcl.1 X hX)),
          List.map_append, <- bindF_map, <- bind_map, <- substList_eq_map, <- substList_eq_map, hv]
      . have e := congrArg (Ty.substList s.ty) h6
        rw [substList_subst_gen (fun X hX => hfst X (hcl.2 X hX)), List.map_append, <- bindF_map, <- bind_map,
          <- substList_eq_map, <- substList_eq_map, hv] at e
        rw [dom_bounds_subst, e, Ty.substList, params_T_subst]


mutual
theorem Expr.noShadow_gsubst {s : GSubst} : forall (e : Expr) {Xs : List TVarName} {xs : List VarName},
    (e.gsubst s).noShadow Xs xs = e.noShadow Xs xs
  | .var _, _, _ => rfl
  | .call e _ _ es, _, _ => by simp only [Expr.gsubst, Expr.noShadow, Expr.noShadow_gsubst e, Expr.noShadowList_gsubst es]
  | .superCall e _ _ _ es, _, _ => by
    simp only [Expr.gsubst, Expr.noShadow, Expr.noShadow_gsubst e, Expr.noShadowList_gsubst es]
  | .field e _, _, _ => by simp only [Expr.gsubst, Expr.noShadow, Expr.noShadow_gsubst e]
  | .new _ _ es, _, _ => by simp only [Expr.gsubst, Expr.noShadow, Expr.noShadowList_gsubst es]
  | .newLocal _ _ _ _ es Ms, _, _ => by
    simp only [Expr.gsubst, Expr.noShadow, Expr.noShadowList_gsubst es, Method.noShadowList_gsubst Ms]
  | .ifInst e0 _ _ e1 e2, _, _ => by
    simp only [Expr.gsubst, Expr.noShadow, Expr.noShadow_gsubst e0, Expr.noShadow_gsubst e1, Expr.noShadow_gsubst e2]
theorem Expr.noShadowList_gsubst {s : GSubst} : forall (es : List Expr) {Xs : List TVarName} {xs : List VarName},
    Expr.noShadowList Xs xs (Expr.gsubstList s es) = Expr.noShadowList Xs xs es
  | [], _, _ => rfl
  | e :: es, _, _ => by simp only [Expr.gsubstList, Expr.noShadowList, Expr.noShadow_gsubst e, Expr.noShadowList_gsubst es]
theorem Method.noShadow_gsubst {s : GSubst} : forall (M : Method) {Xs : List TVarName} {xs : List VarName},
    (M.gsubst s).noShadow Xs xs = M.noShadow Xs xs
  | .mk _ _ _ _ e, _, _ => by
    simp only [Method.gsubst, Method.noShadow, dom_bounds_subst, names_subst, Expr.noShadow_gsubst e]
theorem Method.noShadowList_gsubst {s : GSubst} : forall (Ms : List Method) {Xs : List TVarName} {xs : List VarName},
    Method.noShadowList Xs xs (Method.gsubstList s Ms) = Method.noShadowList Xs xs Ms
  | [], _, _ => rfl
  | M :: Ms, _, _ => by
    simp only [Method.gsubstList, Method.noShadowList, Method.noShadow_gsubst M, Method.noShadowList_gsubst Ms]
end

mutual
theorem Expr.uniq_gsubst {s : GSubst} : forall (e : Expr), (e.gsubst s).uniq = e.uniq
  | .var _ => rfl
  | .call e _ _ es => by simp only [Expr.gsubst, Expr.uniq, Expr.uniq_gsubst e, Expr.uniqList_gsubst es]
  | .superCall e _ _ _ es => by simp only [Expr.gsubst, Expr.uniq, Expr.uniq_gsubst e, Expr.uniqList_gsubst es]
  | .field e _ => by simp only [Expr.gsubst, Expr.uniq, Expr.uniq_gsubst e]
  | .new _ _ es => by simp only [Expr.gsubst, Expr.uniq, Expr.uniqList_gsubst es]
  | .newLocal _ _ _ _ es Ms => by simp only [Expr.gsubst, Expr.uniq, Expr.uniqList_gsubst es, Method.uniqList_gsubst Ms]
  | .ifInst e0 _ _ e1 e2 => by
    simp only [Expr.gsubst, Expr.uniq, Expr.uniq_gsubst e0, Expr.uniq_gsubst e1, Expr.uniq_gsubst e2]
theorem Expr.uniqList_gsubst {s : GSubst} : forall (es : List Expr), Expr.uniqList (Expr.gsubstList s es) = Expr.uniqList es
  | [] => rfl
  | e :: es => by simp only [Expr.gsubstList, Expr.uniqList, Expr.uniq_gsubst e, Expr.uniqList_gsubst es]
theorem Method.uniq_gsubst {s : GSubst} : forall (M : Method), (M.gsubst s).uniq = M.uniq
  | .mk _ _ _ _ e => by simp only [Method.gsubst, Method.uniq, dom_bounds_subst, names_subst, Expr.uniq_gsubst e]
theorem Method.uniqList_gsubst {s : GSubst} : forall (Ms : List Method),
    Method.uniqList (Method.gsubstList s Ms) = Method.uniqList Ms
  | [] => rfl
  | M :: Ms => by simp only [Method.gsubstList, Method.uniqList, Method.uniq_gsubst M, Method.uniqList_gsubst Ms]
end

theorem gsubB_cons_none {s : GSubst} {b : Bound} {Delta : Bounds} (h : Not (List.Mem b.X (s.map Prod.fst))) :
    gsubB s (b :: Delta) = { X := b.X, T := b.T.subst s.ty } :: gsubB s Delta := by
  have : ((s.map Prod.fst).contains b.X) = false := by simpa using h
  simp only [gsubB, List.filter_cons, this, Bool.not_false, ite_true, Bounds.subst, List.map_cons]

theorem gsubB_cons_some {s : GSubst} {b : Bound} {Delta : Bounds} (h : List.Mem b.X (s.map Prod.fst)) :
    gsubB s (b :: Delta) = gsubB s Delta := by
  have : ((s.map Prod.fst).contains b.X) = true := by simpa using h
  simp only [gsubB, List.filter_cons, this, Bool.not_true]
  rfl

theorem mem_gsubB {s : GSubst} {Delta : Bounds} {b : Bound} (hb : List.Mem b Delta)
    (h : Not (List.Mem b.X (s.map Prod.fst))) : List.Mem { X := b.X, T := b.T.subst s.ty } (gsubB s Delta) := by
  simp only [gsubB, Bounds.subst, listMem_iff, List.mem_map, List.mem_filter]
  exact Exists.intro b (And.intro (And.intro hb (by simpa using h)) rfl)

theorem Pairing.gsub {s : GSubst} {Delta : Bounds} {Fs : List Funnel} {Ts : List Ty} {Delta' : Bounds} {Ts'' : List Ty}
    (h : Pairing Delta Fs Ts Delta' Ts'') : Ts = abs Fs -> exists Ts3,
      Pairing (gsubB s Delta) (Fs.map (Funnel.gsubst s)) (abs (Fs.map (Funnel.gsubst s))) (gsubB s Delta') Ts3 := by
  induction h with
  | nil => intro _; exact Exists.intro [] Pairing.nil
  | @funnel X T T0 Fs Ts Delta' Ts' hm _ ih =>
    intro he
    simp only [abs, List.map_cons, Funnel.abs, List.cons.injEq] at he
    rcases ih he.2 with ⟨Ts3, hp⟩
    cases hl : List.lookup X s with
    | none =>
      have hX : Not (List.Mem X (s.map Prod.fst)) := fun hm' => by
        cases lookup_isSome hm' with | intro v hv => rw [hv] at hl; cases hl
      rw [gsubB_cons_none (b := { X := X, T := T }) hX]
      simp only [List.map_cons, Funnel.gsubst, hl, abs, Funnel.abs]
      exact Exists.intro _ (Pairing.funnel (mem_gsubB (b := { X := X, T := T }) hm hX) hp)
    | some G =>
      rw [gsubB_cons_some (b := { X := X, T := T }) (lookup_some_mem_dom hl)]
      simp only [List.map_cons, Funnel.gsubst, hl, abs, Funnel.abs]
      exact Exists.intro _ (Pairing.ground hp)
  | @ground G Fs Ts Delta' Ts' _ ih =>
    intro he
    simp only [abs, List.map_cons, Funnel.abs, List.cons.injEq] at he
    rcases ih he.2 with ⟨Ts3, hp⟩
    simp only [List.map_cons, Funnel.gsubst, abs, Funnel.abs]
    exact Exists.intro _ (Pairing.ground hp)

theorem innerG_gsub_sub {s : GSubst} {gamma : Gamma} {Fs : List Funnel} {C : ClassName} :
    Sub1 (gsubG s (innerG gamma Fs C)) (innerG (gsubG s gamma) (Fs.map (Funnel.gsubst s)) C) := by
  intro y hy
  simp only [innerG, gsubG, withoutThis, restrict, listMem_iff, List.map_append, List.mem_append, List.mem_map,
    List.mem_filter, List.map_cons, List.map_nil, List.mem_singleton] at hy |-
  rcases hy with hy | hy
  . cases hy with
    | intro z hz =>
      refine Or.inl (And.intro (And.intro (Exists.intro z (And.intro hz.1.1.1 hz.2)) ?_) ?_)
      . rw [<- hz.2, List.all_eq_true]
        intro X hX
        have hA := hz.1.1.2
        rw [List.all_eq_true] at hA
        have h1 := Ty.ftv_gsubst (s := s) (T := z.T) (by simpa [VarDecl.subst] using hX)
        have h2 := hA X h1.1
        simp only [List.contains_iff_mem] at h2 |-
        rw [abs_gsubst]
        exact Ty.ftvList_gsubst_back h2 h1.2
      . rw [<- hz.2]; simpa [VarDecl.subst] using hz.1.2
  . refine Or.inr ?_
    rw [hy]
    simp only [VarDecl.subst, Ty.subst, abs_gsubst]

theorem Consistent.gsub {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {s : GSubst}
    {C : ClassName} {Fs : List Funnel} {C0 : ClassName} {Ts : List Ty} {es es' : List Expr} {Ms : List Method}
    (h : Consistent d (.loc C Fs C0 Ts es Ms))
    (hdis : forall M, List.Mem M Ms -> forall X, List.Mem X (dom M.bounds) -> Not (List.Mem X (s.map Prod.fst))) :
    Consistent d (.loc C (Fs.map (Funnel.gsubst s)) C0 (Ty.substList s.ty Ts) es' (Method.gsubstList s Ms)) := by
  rcases consistent_unfold h with ⟨Fs', h⟩; cases h with
  | intro Ts' h => cases h with
    | intro es'' h => cases h with
      | intro Ms'' h =>
        have hcl := hd.supL _ _ _ _ _ _ h.1
        refine Exists.intro Fs' (Exists.intro Ts' (Exists.intro es'' (Exists.intro Ms'' (And.intro h.1
          (And.intro (by simp [h.2.1]) (And.intro ?_ (And.intro ?_ ?_)))))))
        . rw [abs_gsubst, h.2.2.1, substList_subst_gen (fun X hX => by
            cases bindF_lookup_some (Us := abs Fs) (by rw [abs_length]; exact h.2.1) (hcl X hX) with
            | intro U hU => exact lookup_some_mem_dom hU), <- bindF_map, <- substList_eq_map]
        . intro m; rw [names_gsubst]; exact h.2.2.2.1 m
        . intro M' hM'
          rw [abs_gsubst]
          cases gsubstList_mem hM' with
          | intro M hM => rw [hM.2]; exact OverrideOkM.gsubst hwf hok (h.2.2.2.2 M hM.1) (hdis M hM.1)

theorem OverrideOk.gsub {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {s : GSubst}
    {Delta Delta2 : Bounds} {C0 : ClassName} {Ts : List Ty} {Ms : List Method} (h : OverrideOk d Delta (.cls C0 Ts) Ms)
    (hdis : forall M, List.Mem M Ms -> forall X, List.Mem X (dom M.bounds) -> Not (List.Mem X (s.map Prod.fst))) :
    OverrideOk d Delta2 (.cls C0 (Ty.substList s.ty Ts)) (Method.gsubstList s Ms) := by
  intro M' C' Ts' hM' hs
  rcases gsubstList_mem hM' with ⟨M, hM⟩
  rw [hM.2]
  rcases Sub.inv_subst hd (Delta2 := Delta) (A := Ty.ftvList Ts) hs rfl (fun _ h => h) with ⟨T0, h0⟩
  rcases Sub.cls_target h0.2.1 rfl with ⟨C1, h1⟩; cases h1 with
  | intro U0 e0 =>
    subst e0
    have e := h0.1
    simp only [Ty.subst, Ty.cls.injEq] at e
    have e1 := e.1
    subst e1
    rw [e.2]
    exact OverrideOkM.gsubst hwf hok (h M C' U0 hM.1 h0.2.1) (hdis M hM.1)


theorem dom_mem_tbinders {X : TVarName} : forall {M : Method}, List.Mem X (dom M.bounds) -> List.Mem X M.tbinders
  | .mk _ _ _ _ _, h => by
    simp only [Method.bounds] at h
    simp only [Method.tbinders, listMem_iff, List.mem_append]
    exact Or.inl h

theorem Typing.gsub_newLocal {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {Delta : Bounds}
    {gamma : Gamma} {C : ClassName} {Fs : List Funnel} {C0 : ClassName} {Ts : List Ty} {es : List Expr}
    {Ms : List Method} {Delta' : Bounds} {Ts'' : List Ty} {T'' : Ty} {s : GSubst} {Xs : List TVarName}
    {xs : List VarName}
    (h1 : Consistent d (.loc C Fs C0 Ts es Ms)) (h2 : Pairing Delta Fs (abs Fs) Delta' Ts'')
    (h3 : forall X, List.Mem X (Ty.ftvList (cod Delta')) -> List.Mem X (dom Delta'))
    (h4 : Kind d Delta' (.cls C (abs Fs))) (h5 : Kind d Delta' (.cls C0 Ts))
    (h8 : OverrideOk d Delta' (.cls C0 Ts) Ms)
    (ih6 : Typing d (gsubB s Delta) (gsubG s gamma) ((Expr.new C0 Ts es).gsubst s) (T''.subst s.ty))
    (ih7 : forall M, List.Mem M Ms -> MethodOk d (gsubB s Delta') (gsubG s (innerG gamma Fs C)) (M.gsubst s))
    (hg : GOk d Delta s)
    (hdis : forall X, List.Mem X (Expr.newLocal C Fs C0 Ts es Ms).tbinders -> Not (List.Mem X (s.map Prod.fst)))
    (n1 : (gdom gamma).Nodup) (sc : Sub1 (gdom gamma) xs) (hn : (Expr.newLocal C Fs C0 Ts es Ms).noShadow Xs xs = true)
    (ht : NoThis (Expr.newLocal C Fs C0 Ts es Ms)) (hu : (Expr.newLocal C Fs C0 Ts es Ms).uniq) :
    Typing d (gsubB s Delta) (gsubG s gamma) ((Expr.newLocal C Fs C0 Ts es Ms).gsubst s)
      ((Ty.cls C (abs Fs)).subst s.ty) := by
  simp only [Expr.noShadow, Bool.and_eq_true] at hn
  simp only [Expr.tbinders, listMem_iff, List.mem_append] at hdis
  simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht
  simp only [Expr.uniq] at hu
  have hdisM : forall M, List.Mem M Ms -> forall X, List.Mem X (dom M.bounds) -> Not (List.Mem X (s.map Prod.fst)) :=
    fun M hM X hX => hdis X (Or.inr (tbindersListM_mem hM (dom_mem_tbinders hX)))
  have hg' := hg.mono h2.sub
  have sc' := hg'.substCtx
  simp only [Expr.gsubst] at ih6 |-
  simp only [Ty.subst]
  rw [<- abs_gsubst]
  rcases Pairing.gsub (s := s) h2 rfl with ⟨Ts3, hp⟩
  refine Typing.newLocal (Consistent.gsub hwf hok hd h1 hdisM) hp ?_ ?_ ?_ ih6 ?_ (OverrideOk.gsub hwf hok hd h8 hdisM)
  . intro X hX
    rw [cod_subst] at hX
    have h1' := Ty.ftvList_gsubst hX
    have h2' : List.Mem X (dom Delta') := by
      apply h3
      rcases ftvList_mem.mp h1'.1 with ⟨T, hT⟩
      refine ftvList_mem.mpr (Exists.intro T (And.intro ?_ hT.2))
      simp only [cod, listMem_iff, List.mem_map, List.mem_filter] at hT |-
      rcases hT.1 with ⟨b, hb⟩; exact Exists.intro b (And.intro hb.1.1 hb.2)
    simp only [dom, listMem_iff, List.mem_map] at h2'
    rcases h2' with ⟨b, hb⟩
    have := mem_gsubB (s := s) hb.1 (by rw [hb.2]; exact h1'.2)
    rw [<- hb.2]
    show List.Mem (({ X := b.X, T := Ty.subst s.ty b.T } : Bound).X) (dom (gsubB s Delta'))
    exact List.mem_map_of_mem (f := Bound.X) this
  . have := Kind.subst hd sc'.sub sc'.kind h4
    simp only [Ty.subst] at this
    rw [abs_gsubst]
    exact this
  . have := Kind.subst hd sc'.sub sc'.kind h5
    simp only [Ty.subst] at this
    exact this
  . intro M' hM'
    rcases gsubstList_mem hM' with ⟨M, hM⟩
    rw [hM.2]
    have hnM := noShadowListM_mem hM.1 hn.2
    have htM : NoThisM M := fun h => ht.2 (vbindersListM_mem hM.1 h)
    have sc2 : Sub1 (gdom (gsubG s gamma)) xs := by rw [gdom_gsubG]; exact sc
    refine MethodOk.weak (ih7 M hM.1) (fun _ h => h) innerG_gsub_sub
      (by rw [gdom_gsubG]; exact innerG_nodup n1 _ _)
      (innerG_nodup (by rw [gdom_gsubG]; exact n1) _ _)
      (by rw [gdom_gsubG]; exact innerG_dom sc _ _)
      (by rw [Method.noShadow_gsubst]; exact hnM) ?_
      (by simp only [NoThisM]; rw [Method.vbinders_gsubst]; exact htM)
      (by rw [Method.uniq_gsubst]; exact uniqList_mem hM.1 hu.2)
    intro y hy hm
    rw [Method.vbinders_gsubst] at hy
    have hyt : Not (y = this) := fun e => htM (e ▸ hy)
    cases innerG_dom sc2 (Fs.map (Funnel.gsubst s)) C y hm with
    | head => exact hyt rfl
    | tail _ h => exact Method.noShadow_binders hnM htM y hy h

end Funnelling.High
