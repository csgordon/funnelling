import Funnelling.Sound.Unique

open Funnelling.SoundSimp

namespace Funnelling.High

theorem pairing_funnels {Delta : Bounds} {Fs : List Funnel} {Ts : List Ty} {D0 : Bounds} {T0 : List Ty}
    (h : Pairing Delta Fs Ts D0 T0) (hf : forall F, List.Mem F Fs -> F.isFunnel = true) : T0 = Ts := by
  induction h with
  | nil => rfl
  | funnel _ _ ih => rw [ih (fun F hF => hf F (List.Mem.tail _ hF))]
  | ground _ _ => have := hf _ (List.Mem.head _); simp [Funnel.isFunnel] at this

theorem bindF_funnels : forall {Fs : List Funnel} {Ts : List Ty}, (forall F, List.Mem F Fs -> F.isFunnel = true) ->
    bindF Fs Ts = (domF Fs).zip Ts
  | [], _, _ => by simp [bindF, domF]
  | _ :: _, [], _ => by simp [bindF, domF]
  | F :: Fs, T :: Ts, hf => by
    cases F with
    | ground G => have := hf _ (List.Mem.head _); simp [Funnel.isFunnel] at this
    | funnel X =>
      have ih := bindF_funnels (Fs := Fs) (Ts := Ts) (fun F hF => hf F (List.Mem.tail _ hF))
      simp only [bindF, domF, List.zip_cons_cons, List.filterMap_cons] at ih |-
      rw [ih]

theorem bind_eq_bindF {Dl : Bounds} {Fs : List Funnel} (hg : dom Dl = domF Fs)
    (hall : forall F, List.Mem F Fs -> F.isFunnel = true) (Ts : List Ty) : bind Dl Ts = bindF Fs Ts := by
  rw [bindF_funnels hall]
  simp only [bind]
  rw [hg]

theorem kind_chain {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {Delta : Bounds}
    {C : ClassName} {Ts : List Ty} {T2 : Ty} (hk : Kind d Delta (.cls C Ts)) (h : Sub d Delta (.cls C Ts) T2) :
    Kind d Delta T2 := by
  generalize he : Ty.cls C Ts = T1 at h hk
  induction h generalizing C Ts with
  | subRefl => exact hk
  | @subInherit D Ts0 T' hD hl _ ih =>
    have hka := kind_dec_args hwf hD hk
    have hcls := (hok D hD.dec_mem).2.1 _ (List.Mem.head _)
    have hK := Kind.subst hd (Delta' := Delta) (s := bind D.bounds Ts0) (fun b hb => (hka.2 b hb).1)
      (fun b hb => (hka.2 b hb).2) hcls
    simp only [Ty.subst] at hK
    exact ih rfl hK
  | @subInheritLocal C1 Fs C' Ts' es Ms Ts1 T' hD hl _ ih =>
    cases hk with
    | @wfClass C9 Ts9 Dl0 Ts0 h1 h2 h3 h4 =>
      rcases h1.loc_declared with h' | h'
      . cases h' with
        | intro D hD' => exact absurd (Declared.dec_loc hwf hD'.1 hD hD'.2.1) id
      . cases scopeFacts hwf hok h1 with
        | intro k' hk' =>
          have hname : k'.name = C1 := by
            rcases hk'.2.1 with ⟨Us, hUs⟩; simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
          have ek := Declared.unique hwf hk'.1 hD hname
          subst ek
          have sf := hk'.2.2
          have hall : forall F, List.Mem F Fs -> F.isFunnel = true :=
            fun F hF => hwf.2.2.2.2.2.2.2.2.2.2 _ hD.mem F hF
          cases h' with
          | intro Fs2 h' => cases h' with
            | intro C2 h' => cases h' with
              | intro Ts2 h' => cases h' with
                | intro es2 h' => cases h' with
                  | intro Ms2 h' => cases h' with
                    | intro Dl hp =>
                      have ek2 := Declared.unique hwf hp.1 hD rfl
                      cases ek2
                      have e0 := pairing_funnels hp.2 hall
                      subst e0
                      have hsat := bounds_sat sf.ndom h3 h4 h2
                      have hK := Kind.subst hd (Delta' := Delta) (fun b hb => (hsat b hb).1)
                        (fun b hb => (hsat b hb).2) (sf.supK _ _ _ _ _ _ rfl)
                      rw [bind_eq_bindF sf.gv hall] at hK
                      exact ih rfl hK
  | subVar => cases he

theorem kind_len {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {C : ClassName} {Us : List Ty} {Xs : List TVarName}
    (hk : Kind d Delta (.cls C Us)) (hg : Generic d C (.cls C (vars Xs))) : Us.length = Xs.length := by
  generalize hgT : Ty.cls C (vars Xs) = T at hg
  cases hk with
  | wfClass h1 h2 h3 h4 =>
    cases hg with
    | @dec D hD =>
      simp only [Ty.cls.injEq] at hgT
      have hlx := congrArg List.length hgT.2
      simp only [vars, List.length_map, dom] at hlx
      have e := Scope.dec_eq hwf hD h1
      rw [e.1, e.2] at h3
      rw [h3, hlx]
    | @loc C0 Fs C' Ts' es Ms hD =>
      simp only [Ty.cls.injEq] at hgT
      have hlx := congrArg List.length hgT.2
      simp only [vars, List.length_map] at hlx
      rcases h1.loc_declared with h' | h'
      . cases h' with
        | intro D hD' => exact absurd (Declared.dec_loc hwf hD'.1 hD hD'.2.1) id
      . cases h' with
        | intro Fs2 h' => cases h' with
          | intro C2 h' => cases h' with
            | intro Ts2 h' => cases h' with
              | intro es2 h' => cases h' with
                | intro Ms2 h' => cases h' with
                  | intro Dl hp =>
                    have ek2 := Declared.unique hwf hp.1 hD rfl
                    cases ek2
                    have hall : forall F, List.Mem F Fs -> F.isFunnel = true :=
                      fun F hF => hwf.2.2.2.2.2.2.2.2.2.2 _ hD.mem F hF
                    have e0 := pairing_funnels hp.2 hall
                    rw [e0] at h3
                    have hd := congrArg List.length hp.2.dom_eq
                    simp only [dom, List.length_map] at hd
                    rw [h3, hd, hlx]

theorem sub_unique {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {k : K} (hk : Declared d k) {Ts : List Ty}
    {C' : ClassName} {U1 U2 : List Ty} (h1 : Sub d Delta (.cls k.name Ts) (.cls C' U1))
    (h2 : Sub d Delta (.cls k.name Ts) (.cls C' U2)) : U1 = U2 := by
  cases k with
  | dec D => exact sub_unique_dec hwf (Exists.intro D (Exists.intro Ts (And.intro hk rfl))) h1 h2
  | loc C Fs C0 Ts0 es Ms =>
    simp only [K.name] at h1 h2
    rcases Declared.super hwf hk with ⟨D', hD'⟩
    have hsup := hD'.2
    simp only [K.sup] at hsup
    have back : forall {U : List Ty}, Sub d Delta ((Ty.cls C0 Ts0).subst (bindF Fs Ts)) (.cls C U) -> False := by
      intro U hs
      simp only [Ty.subst] at hs
      rw [<- hsup] at hs
      rcases Sub.top_target hwf hD'.1 hs with ⟨D0, hD0⟩; exact Declared.dec_loc hwf hD0.1 hk hD0.2
    rcases Sub.loc_step hwf hk h1 with e1 | s1
    . rcases Sub.loc_step hwf hk h2 with e2 | s2
      . simp only [Ty.cls.injEq] at e1 e2; rw [e1.2, e2.2]
      . simp only [Ty.cls.injEq] at e1; rw [e1.1] at s2; exact absurd (back s2.2) id
    . rcases Sub.loc_step hwf hk h2 with e2 | s2
      . simp only [Ty.cls.injEq] at e2; rw [e2.1] at s1; exact absurd (back s1.2) id
      . refine sub_unique_dec hwf ?_ s1.2 s2.2
        refine Exists.intro D' (Exists.intro (Ty.substList (bindF Fs Ts) Ts0) (And.intro hD'.1 ?_))
        simp only [Ty.subst]; rw [hsup]

theorem var_subst_cons_ne {X Y : TVarName} {U : Ty} {r : TSubst} (h : Not (Y = X)) :
    (Ty.var Y).subst ((X, U) :: r) = (Ty.var Y).subst r := by
  simp only [Ty.subst, lookup_cons_ne h]

theorem vars_subst : forall {Xs : List TVarName} {Us : List Ty}, Xs.Nodup -> Us.length = Xs.length ->
    Ty.substList (Xs.zip Us) (vars Xs) = Us
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | X :: Xs, U :: Us, hn, hl => by
    simp only [vars, List.map_cons, List.zip_cons_cons, Ty.substList]
    have h1 : (Ty.var X).subst ((X, U) :: Xs.zip Us) = U := by simp only [Ty.subst, lookup_cons_eq]; rfl
    rw [h1]
    have ih := vars_subst (List.nodup_cons.mp hn).2 (by simpa using hl)
    simp only [vars] at ih
    have h2 : Ty.substList ((X, U) :: Xs.zip Us) (Xs.map Ty.var) = Ty.substList (Xs.zip Us) (Xs.map Ty.var) := by
      rw [substList_eq_map, substList_eq_map]
      apply List.map_congr_left
      intro T hT
      rcases List.mem_map.mp hT with ⟨Y, hY⟩
      rw [<- hY.2]
      exact var_subst_cons_ne (fun e => (List.nodup_cons.mp hn).1 (e ▸ hY.1))
    rw [h2, ih]

mutual
theorem subst_agree {s1 s2 : TSubst} : forall {T : Ty}, T.subst s1 = T.subst s2 ->
    forall X, List.Mem X T.ftv -> (Ty.var X).subst s1 = (Ty.var X).subst s2
  | .var Y, h, X, hX => by
    have e : X = Y := by simpa [Ty.ftv] using hX
    rw [e]; exact h
  | .cls C Ts, h, X, hX => by
    simp only [Ty.subst, Ty.cls.injEq] at h
    exact substList_agree h.2 X (by simpa [Ty.ftv] using hX)
theorem substList_agree {s1 s2 : TSubst} : forall {Ts : List Ty}, Ty.substList s1 Ts = Ty.substList s2 Ts ->
    forall X, List.Mem X (Ty.ftvList Ts) -> (Ty.var X).subst s1 = (Ty.var X).subst s2
  | [], _, _, hX => by cases hX
  | T :: Ts, h, X, hX => by
    simp only [Ty.substList, List.cons.injEq] at h
    simp only [Ty.ftvList, listMem_iff, List.mem_append] at hX
    rcases hX with hX | hX
    . exact subst_agree h.1 X hX
    . exact substList_agree h.2 X hX
end

theorem list_eq_of_pointwise : forall {Xs : List TVarName} {Ts Us : List Ty}, Xs.Nodup -> Ts.length = Xs.length ->
    Us.length = Xs.length -> (forall X, List.Mem X Xs -> (Ty.var X).subst (Xs.zip Ts) = (Ty.var X).subst (Xs.zip Us)) ->
    Ts = Us
  | [], [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _, _ => by simp at h
  | [], _, _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _, _ => by simp at h
  | _ :: _, _, [], _, _, h, _ => by simp at h
  | X :: Xs, T :: Ts, U :: Us, hn, h1, h2, hp => by
    have hh := hp X (List.Mem.head _)
    simp only [List.zip_cons_cons, Ty.subst, lookup_cons_eq, Option.getD_some] at hh
    have ih := list_eq_of_pointwise (Xs := Xs) (Ts := Ts) (Us := Us) (List.nodup_cons.mp hn).2 (by simpa using h1) (by simpa using h2) (fun Y hY => by
      have e := hp Y (List.Mem.tail _ hY)
      have hne : Not (Y = X) := fun e' => (List.nodup_cons.mp hn).1 (e' ▸ hY)
      simp only [List.zip_cons_cons] at e
      rwa [var_subst_cons_ne hne, var_subst_cons_ne hne] at e)
    rw [hh, ih]

theorem vars_inj : forall {Xs Ys : List TVarName}, vars Xs = vars Ys -> Xs = Ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [vars] at h
  | _ :: _, [], h => by simp [vars] at h
  | X :: Xs, Y :: Ys, h => by
    simp only [vars, List.map_cons, List.cons.injEq, Ty.var.injEq] at h
    have ih := vars_inj (Xs := Xs) (Ys := Ys) (by simpa [vars] using h.2)
    rw [h.1, ih]

theorem Generic.nodup {d : Decls} (hwf : WFDecls d) {C : ClassName} {Xs : List TVarName}
    (hg : Generic d C (.cls C (vars Xs))) : Xs.Nodup /\ exists k, Declared d k /\ k.name = C := by
  generalize hgT : Ty.cls C (vars Xs) = T at hg
  cases hg with
  | @dec D hD =>
    simp only [Ty.cls.injEq] at hgT
    have hx : Xs = dom D.bounds := by
      have := hgT.2
      simp only [vars] at this
      exact vars_inj this
    refine And.intro ?_ (Exists.intro _ (And.intro hD rfl))
    rw [hx]
    exact hwf.2.2.2.2.1 D.bounds (by
      simp only [listMem_iff, List.mem_append, List.mem_map]
      exact Or.inl (Exists.intro D (And.intro hD.dec_mem rfl)))
  | @loc C0 Fs C' Ts' es Ms hD =>
    simp only [Ty.cls.injEq] at hgT
    have hx : Xs = domF Fs := by
      have := hgT.2
      simp only [vars] at this
      exact vars_inj this
    refine And.intro ?_ (Exists.intro _ (And.intro hD rfl))
    rw [hx]
    exact hwf.2.2.2.2.2.1 _ hD.mem

theorem cast_runtime {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {T0 : Ty} {C : ClassName}
    {Ts Ts'' : List Ty} {k1 : K} {U1 : List Ty} (hk1d : Declared d k1) (hc : Cast d [] T0 (.cls C Ts))
    (hv : Sub d [] (.cls k1.name U1) T0) (hr : Sub d [] (.cls k1.name U1) (.cls C Ts''))
    (hk : Kind d [] (.cls C Ts)) (hk1 : Kind d [] (.cls k1.name U1)) : Sub d [] (.cls k1.name U1) (.cls C Ts) := by
  cases hc with
  | castUp h => exact hv.trans h
  | castVar hm => cases hm
  | @castDown C9 Ts9 C' Ts0 Xs Ts' h1 h2 h3 h4 =>
    have hg := Generic.nodup hwf h2
    have hk2 := kind_chain hwf hok hd hk1 hr
    have l1 := kind_len hwf hk h2
    have l2 := kind_len hwf hk2 h2
    have hs1 := Sub.subst hd (Delta' := []) (s := Xs.zip Ts) (fun b hb => by cases hb) h3
    have hs2 := Sub.subst hd (Delta' := []) (s := Xs.zip Ts'') (fun b hb => by cases hb) h3
    simp only [Ty.subst] at hs1 hs2
    rw [vars_subst hg.1 l1] at hs1
    rw [vars_subst hg.1 l2] at hs2
    rcases hg.2 with ⟨k, hk'⟩
    have hkn := hk'.2
    rw [<- hkn] at hs1 hs2 h1
    have e1 := sub_unique hwf hk'.1 h1 hs1
    have hr' := hr
    rw [<- hkn] at hr'
    have e2 := sub_unique hwf hk1d hv (hr'.trans hs2)
    have eq : Ty.substList (Xs.zip Ts) Ts' = Ty.substList (Xs.zip Ts'') Ts' := by rw [<- e1, <- e2]
    have hts := list_eq_of_pointwise hg.1 l1 l2 (fun X hX => substList_agree eq X (h4 X hX))
    rw [hts]
    exact hr

end Funnelling.High