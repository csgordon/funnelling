import Funnelling.Sound.RenT

open Funnelling.SoundSimp

namespace Funnelling.High

mutual
theorem Ty.ftv_subst_sub {s : TSubst} {A : List TVarName} : forall {T : Ty},
    (forall Y, List.Mem Y T.ftv -> forall X, List.Mem X ((Ty.var Y).subst s).ftv -> List.Mem X A) ->
    forall X, List.Mem X (T.subst s).ftv -> List.Mem X A
  | .var Y, h, X, hX => h Y (List.Mem.head _) X hX
  | .cls C Ts, h, X, hX => by
    exact Ty.ftvList_subst_sub h X hX
theorem Ty.ftvList_subst_sub {s : TSubst} {A : List TVarName} : forall {Ts : List Ty},
    (forall Y, List.Mem Y (Ty.ftvList Ts) -> forall X, List.Mem X ((Ty.var Y).subst s).ftv -> List.Mem X A) ->
    forall X, List.Mem X (Ty.ftvList (Ty.substList s Ts)) -> List.Mem X A
  | [], _, _, h => by cases h
  | T :: Ts, h, X, hX => by
    simp only [Ty.substList, Ty.ftvList, listMem_iff, List.mem_append] at hX h
    rcases hX with hX | hX
    . exact Ty.ftv_subst_sub (fun Y hY => h Y (Or.inl hY)) X hX
    . exact Ty.ftvList_subst_sub (fun Y hY => h Y (Or.inr hY)) X hX
end

theorem ftv_var_subst {s : TSubst} {Y X : TVarName} {U : Ty} (hl : List.lookup Y s = some U)
    (hX : List.Mem X ((Ty.var Y).subst s).ftv) : List.Mem X U.ftv := by
  simp only [Ty.subst, hl, Option.getD_some] at hX
  exact hX

theorem mem_bind_snd {A : Type} {Dl : Bounds} {Us : List A} {Y : TVarName} {U : A} (h : List.Mem (Y, U) (bind Dl Us)) :
    List.Mem U Us := (List.of_mem_zip h).2

theorem mem_bindF_snd : forall {Fs : List Funnel} {Us : List Ty} {Y : TVarName} {U : Ty},
    List.Mem (Y, U) (bindF Fs Us) -> List.Mem U Us
  | [], _, _, _, h => by simp [bindF] at h
  | _ :: _, [], _, _, h => by simp [bindF] at h
  | F :: Fs, U' :: Us, Y, U, h => by
    cases F with
    | funnel X =>
      have e : bindF (.funnel X :: Fs) (U' :: Us) = (X, U') :: bindF Fs Us := by simp [bindF]
      rw [e] at h
      cases h with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail _ (mem_bindF_snd h)
    | ground G =>
      have e : bindF (.ground G :: Fs) (U' :: Us) = bindF Fs Us := by simp [bindF]
      rw [e] at h
      exact List.Mem.tail _ (mem_bindF_snd h)

theorem ftv_bind_sub {Dl : Bounds} {Us : List Ty} {L : List Ty} (hl : Us.length = Dl.length)
    (hL : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom Dl)) :
    forall X, List.Mem X (Ty.ftvList (Ty.substList (bind Dl Us) L)) -> List.Mem X (Ty.ftvList Us) := by
  refine Ty.ftvList_subst_sub (fun Y hY X hX => ?_)
  cases bind_lookup_some hl (hL Y hY) with
  | intro U hU => exact ftvList_mem.mpr (Exists.intro U (And.intro (mem_bind_snd (lookup_mem hU)) (ftv_var_subst hU hX)))

theorem ftv_bindF_sub {Fs : List Funnel} {Us : List Ty} {L : List Ty} (hl : Us.length = Fs.length)
    (hL : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (domF Fs)) :
    forall X, List.Mem X (Ty.ftvList (Ty.substList (bindF Fs Us) L)) -> List.Mem X (Ty.ftvList Us) := by
  refine Ty.ftvList_subst_sub (fun Y hY X hX => ?_)
  cases bindF_lookup_some hl (hL Y hY) with
  | intro U hU => exact ftvList_mem.mpr (Exists.intro U (And.intro (mem_bindF_snd (lookup_mem hU)) (ftv_var_subst hU hX)))

theorem Sub.inv_subst {d : Decls} (hd : DeclOk d) {Delta Delta2 : Bounds} {s : TSubst} {A : List TVarName}
    {T1 T' : Ty} (h : Sub d Delta T1 T') : forall {C : ClassName} {Ts : List Ty}, T1 = .cls C (Ty.substList s Ts) ->
    (forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X A) ->
    exists T0, T' = T0.subst s /\ Sub d Delta2 (.cls C Ts) T0 /\ forall X, List.Mem X T0.ftv -> List.Mem X A := by
  induction h with
  | subRefl =>
    intro C Ts he hA
    subst he
    exact Exists.intro (.cls C Ts) (And.intro (by simp only [Ty.subst]) (And.intro Sub.subRefl hA))
  | @subInherit D Ts0 T' hD hl _ ih =>
    intro C Ts he hA
    simp only [Ty.cls.injEq] at he
    have e1 := he.1
    have e2 := he.2
    subst e1 e2
    have hl' : Ts.length = D.bounds.length := by rw [<- hl, substList_length]
    have heq : (Ty.cls D.C' D.Ts).subst (bind D.bounds (Ty.substList s Ts)) =
        .cls D.C' (Ty.substList s (Ty.substList (bind D.bounds Ts) D.Ts)) := by
      simp only [Ty.subst]
      rw [substList_bind_comp hl' (hd.supD D hD)]
    cases ih heq (fun X hX => ftv_bind_sub hl' (hd.supD D hD) X hX |> fun h => ftvList_mem.mp h |> fun h => by
        cases h with | intro U hU => exact hA X (ftvList_mem.mpr (Exists.intro U hU))) with
    | intro T0 h0 =>
      refine Exists.intro T0 (And.intro h0.1 (And.intro (Sub.subInherit hD hl' ?_) h0.2.2))
      exact h0.2.1
  | @subInheritLocal C0 Fs C' Ts' es Ms Ts0 T' hD hl _ ih =>
    intro C Ts he hA
    simp only [Ty.cls.injEq] at he
    have e1 := he.1
    have e2 := he.2
    subst e1 e2
    have hl' : Ts.length = Fs.length := by rw [<- hl, substList_length]
    have hcl := hd.supL _ _ _ _ _ _ hD
    have heq : (Ty.cls C' Ts').subst (bindF Fs (Ty.substList s Ts)) =
        .cls C' (Ty.substList s (Ty.substList (bindF Fs Ts) Ts')) := by
      simp only [Ty.subst]
      rw [substList_eq_map (Us := Ts'), substList_eq_map (Us := Ty.substList (bindF Fs Ts) Ts'),
        substList_eq_map (Us := Ts'), List.map_map]
      congr 1
      apply List.map_congr_left
      intro T hT
      show _ = (T.subst (bindF Fs Ts)).subst s
      exact (subst_bindF_comp hl' (fun X hX => hcl X (ftvList_mem.mpr (Exists.intro T (And.intro hT hX))))).symm
    rcases ih heq (fun X hX => by exact hA X (ftv_bindF_sub hl' hcl X hX)) with ⟨T0, h0⟩
    refine Exists.intro T0 (And.intro h0.1 (And.intro (Sub.subInheritLocal hD hl' ?_) h0.2.2))
    exact h0.2.1
  | subVar _ _ _ =>
    intro C Ts he
    cases he

theorem map_zip_fst {A B C : Type} {f : A -> C} : forall {l : List A} {l' : List B}, l'.length = l.length ->
    (l.zip l').map (fun p => f p.1) = l.map f
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [map_zip_fst (by simpa using h)]

theorem renList_subst_gen {rt : TRen} {s : TSubst} {L : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (s.map Prod.fst)) :
    Ty.renList rt (Ty.substList s L) = Ty.substList (s.map fun p => (p.1, p.2.ren rt)) L := by
  rw [Ty.renList_subst, Ty.substList_comp (fun X hX => var_subst_comp_of_some (lookup_isSome (h X hX)))]
  simp only [Ty.ren_subst]

theorem map_rn_zip : forall {xs ys : List TVarName} {r : TRen}, xs.Nodup -> xs.length = ys.length ->
    xs.map (rn (xs.zip ys ++ r)) = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, r, hn, hl => by
    simp only [List.zip_cons_cons, List.cons_append, List.map_cons, rn_cons_eq]
    have hn' := List.nodup_cons.mp hn
    have ih := map_rn_zip (r := r) hn'.2 (by simpa using hl)
    have e : xs.map (rn ((x, y) :: (xs.zip ys ++ r))) = xs.map (rn (xs.zip ys ++ r)) := by
      apply List.map_congr_left
      intro z hz
      have hzx : Not (z = x) := fun e => hn'.1 (by rw [<- e]; exact hz)
      exact rn_cons_ne hzx
    rw [e, ih]

theorem ren_vars {xs ys : List TVarName} {r : TRen} (hn : xs.Nodup) (hl : xs.length = ys.length) :
    (vars xs).map (Ty.ren (xs.zip ys ++ r)) = vars ys := by
  have e := map_rn_zip (r := r) hn hl
  simp only [vars, List.map_map]
  conv => rhs; rw [<- e]
  rw [List.map_map]
  rfl

theorem ren_disj {Xs Ys : List TVarName} {r : TRen} {Ts : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList Ts) -> Not (List.Mem X Xs)) :
    Ts.map (Ty.ren (Xs.zip Ys ++ r)) = Ty.renList r Ts := by
  rw [Ty.renList_eq_map]
  apply List.map_congr_left
  intro T hT
  exact Ty.ren_congr (fun X hX => rn_zip_not_mem (h X (ftvList_mem.mpr (Exists.intro T (And.intro hT hX)))))

theorem declMeth_closed {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {k : K} (hk : Declared d k)
    {Dl : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl} {e : Expr} (hM : List.Mem (Method.mk Dl T0 m ps e) k.Ms) :
    (forall X, List.Mem X (Ty.ftvList (cod Dl)) -> List.Mem X (k.gvars ++ dom Dl)) /\
      (forall X, List.Mem X (Ty.ftvList (T0 :: ps.map VarDecl.T)) -> List.Mem X (k.gvars ++ dom Dl)) := by
  rcases scopeExists hwf hok hk with ⟨Dk, h⟩; cases h with
  | intro Tk hs =>
    rcases scopeFacts hwf hok hs with ⟨k', hk'⟩
    have hname : k'.name = k.name := by
      rcases hk'.2.1 with ⟨Us, hUs⟩
      rcases K.generic_name k with ⟨Vs, hVs⟩; rw [hVs] at hUs; simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
    have ek := Declared.unique hwf hk'.1 hk hname
    subst ek
    rcases hk'.2.2.meths _ hM with ⟨gamma, hmo⟩
    have hmi := methodOk_inv hmo
    rw [<- hk'.2.2.gv, <- dom_append]
    refine And.intro ?_ ?_
    . intro X hX
      rcases ftvList_mem.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.1 T hT.1) X hT.2
    . intro X hX
      rcases ftvList_mem.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.2.1 T hT.1) X hT.2

theorem OverrideOkM.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {rv : VRen} {rt : TRen} {C : ClassName}
    {Us : List Ty} {M M' : Method} (h : OverrideOkM d (.cls C Us) M) (hr : RenM rv rt M M')
    (hdis : forall X, List.Mem X (Ty.ftvList Us) -> Not (List.Mem X (dom M.bounds))) (hu : M.uniq) :
    OverrideOkM d (.cls C (Ty.renList rt Us)) M' := by
  cases hr with
  | @mk _ _ Dp T0p m psp ep ep' Xs' xs' hL hl hb =>
    simp only [Method.bounds, Method.uniq] at hdis hu
    have hcod : cod ((Dp.zip Xs').map fun p => ({ X := p.2, T := p.1.T.ren ((dom Dp).zip Xs' ++ rt) } : Bound)) =
        (cod Dp).map (Ty.ren ((dom Dp).zip Xs' ++ rt)) := by
      simp only [cod, List.map_map]; exact map_zip_fst (f := fun b => b.T.ren ((dom Dp).zip Xs' ++ rt)) hL
    have hps : ((psp.zip xs').map fun p => ({ T := p.1.T.ren ((dom Dp).zip Xs' ++ rt), x := p.2 } : VarDecl)).map
        VarDecl.T = (psp.map VarDecl.T).map (Ty.ren ((dom Dp).zip Xs' ++ rt)) := by
      simp only [List.map_map]; exact map_zip_fst (f := fun p => p.T.ren ((dom Dp).zip Xs' ++ rt)) hl
    have hlenD : ((Dp.zip Xs').map fun p => ({ X := p.2, T := p.1.T.ren ((dom Dp).zip Xs' ++ rt) } : Bound)).length =
        Dp.length := by simp [hL]
    have hvars := ren_vars (r := rt) hu.1 (by rw [hL]; simp [dom])
    have hdisj := ren_disj (Ys := Xs') (r := rt) hdis
    cases h with
    | absent h1 h2 => exact OverrideOkM.absent h1 h2
    | @dec D _ _ _ _ _ _ Do T0o pso eo h1 h2 h3 h4 h5 h6 =>
      have hcl := declMeth_closed hwf hok h1 h2
      simp only [K.gvars, <- dom_append] at hcl
      have hlen : (Us ++ vars (dom Dp)).length = (D.bounds ++ Do).length := by simp [h3, h4, vars, dom]
      have hfst := bind_fst (D := D.bounds ++ Do) hlen
      refine OverrideOkM.dec h1 h2 (by rw [renList_length, h3]) (by rw [hlenD, h4]) ?_ ?_
      . rw [dom_renBounds hL, hcod, <- h5, <- Ty.renList_eq_map, renList_subst_gen (fun X hX => hfst ▸ hcl.1 X hX),
          <- bind_map, List.map_append, hvars, hdisj]
      . have e := congrArg (Ty.renList ((dom Dp).zip Xs' ++ rt)) h6
        rw [renList_subst_gen (fun X hX => hfst ▸ hcl.2 X hX), <- bind_map, List.map_append, hvars, hdisj] at e
        rw [dom_renBounds hL, e, Ty.renList, Ty.renList_eq_map, hps]
    | @loc C Fs C0 Ts0 es Ms _ _ _ _ _ _ Do T0o pso eo h1 h2 h3 h4 h5 h6 =>
      have hcl := declMeth_closed hwf hok h1 h2
      have hfst : forall X, List.Mem X (domF Fs ++ dom Do) ->
          List.Mem X ((bindF Fs Us ++ bind Do (vars (dom Dp))).map Prod.fst) := by
        intro X hX
        simp only [listMem_iff, List.mem_append, List.map_append] at hX |-
        rcases hX with hX | hX
        . cases bindF_lookup_some h3 hX with
          | intro U hU => exact Or.inl (lookup_some_mem_dom hU)
        . exact Or.inr (by rw [bind_fst (by simp [h4, vars, dom])]; exact hX)
      refine OverrideOkM.loc h1 h2 (by rw [renList_length, h3]) (by rw [hlenD, h4]) ?_ ?_
      . rw [dom_renBounds hL, hcod, <- h5, <- Ty.renList_eq_map, renList_subst_gen (fun X hX => hfst X (hcl.1 X hX)),
          List.map_append, <- bindF_map, <- bind_map, hvars, hdisj]
      . have e := congrArg (Ty.renList ((dom Dp).zip Xs' ++ rt)) h6
        rw [renList_subst_gen (fun X hX => hfst X (hcl.2 X hX)), List.map_append, <- bindF_map, <- bind_map, hvars,
          hdisj] at e
        rw [dom_renBounds hL, e, Ty.renList, Ty.renList_eq_map, hps]

theorem Consistent.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {rv : VRen} {rt : TRen}
    {C : ClassName} {Fs : List Funnel} {C0 : ClassName} {Ts : List Ty} {es es' : List Expr} {Ms Ms' : List Method}
    (h : Consistent d (.loc C Fs C0 Ts es Ms)) (hr : RenMs rv rt Ms Ms')
    (hdis : forall M, List.Mem M Ms -> forall X, List.Mem X (Ty.ftvList (abs Fs)) -> Not (List.Mem X (dom M.bounds)))
    (hu : forall M, List.Mem M Ms -> M.uniq) :
    Consistent d (.loc C (Fs.map (Funnel.ren rt)) C0 (Ty.renList rt Ts) es' Ms') := by
  rcases consistent_unfold h with ⟨Fs', h⟩; cases h with
  | intro Ts' h => cases h with
    | intro es'' h => cases h with
      | intro Ms'' h =>
        have hcl := hd.supL _ _ _ _ _ _ h.1
        refine Exists.intro Fs' (Exists.intro Ts' (Exists.intro es'' (Exists.intro Ms'' (And.intro h.1
          (And.intro (by simp [h.2.1]) (And.intro ?_ (And.intro ?_ ?_)))))))
        . rw [abs_ren, h.2.2.1, renList_subst_gen (fun X hX => by
            cases bindF_lookup_some (Us := abs Fs) (by rw [abs_length]; exact h.2.1) (hcl X hX) with
            | intro U hU => exact lookup_some_mem_dom hU), <- bindF_map, Ty.renList_eq_map]
        . intro m; rw [RenMs.names hr]; exact h.2.2.2.1 m
        . intro M' hM'
          rw [abs_ren]
          cases RenMs.mem_inv hr hM' with
          | intro M hM => exact OverrideOkM.ren hwf hok (h.2.2.2.2 M hM.1) hM.2 (hdis M hM.1) (hu M hM.1)

theorem OverrideOk.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {rv : VRen} {rt : TRen}
    {Delta Delta' : Bounds} {C0 : ClassName} {Ts : List Ty} {Ms Ms' : List Method}
    (h : OverrideOk d Delta (.cls C0 Ts) Ms) (hr : RenMs rv rt Ms Ms')
    (hdis : forall M, List.Mem M Ms -> forall X, List.Mem X (Ty.ftvList Ts) -> Not (List.Mem X (dom M.bounds)))
    (hu : forall M, List.Mem M Ms -> M.uniq) :
    OverrideOk d Delta' (.cls C0 (Ty.renList rt Ts)) Ms' := by
  intro M' C Ts' hM' hs
  rcases RenMs.mem_inv hr hM' with ⟨M, hM⟩
  rw [Ty.renList_subst] at hs
  rcases Sub.inv_subst hd (Delta2 := Delta) (A := Ty.ftvList Ts) hs rfl (fun _ h => h) with ⟨T0, h0⟩
  cases T0 with
  | var X =>
    have e := h0.1
    rw [lookup_tS] at e
    cases e
  | cls C1 Us =>
    have e := h0.1
    simp only [Ty.subst, Ty.cls.injEq] at e
    have e1 := e.1
    subst e1
    rw [e.2, <- Ty.renList_subst]
    exact OverrideOkM.ren hwf hok (h M C Us hM.1 h0.2.1) hM.2
      (fun X hX => hdis M hM.1 X (h0.2.2 X (by simpa [Ty.ftv] using hX))) (hu M hM.1)

end Funnelling.High
