import Funnelling.Sound.TypeSubstitution

open Funnelling.SoundSimp

namespace Funnelling

theorem Declared.object {d : Decls} (hwf : WFDecls d) {D : Dec} (hD : Declared d (.dec D)) (hO : D.C = Object) :
    D.C' = Object /\ D.Ts = [] /\ D.Delta = [] /\ D.Ms = [] /\ D.Ss = [] := by
  rcases object_declared hwf with ⟨D0, hD0, h1, h2, h3, h4, h5, h6⟩
  have e := ClassDecl.dec.inj (Declared.unique hwf hD hD0 (by show D.C = D0.C; rw [hO, h1]))
  subst e
  exact ⟨h3, h4, h2, h5, h6⟩

theorem sub_from_object {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {U0 : List Ty} {T : Ty}
    (h : Sub d Delta (.cls Object U0) T) : exists U, T = .cls Object U := by
  generalize he : Ty.cls Object U0 = T0 at h
  induction h generalizing U0 with
  | subRefl => exact Exists.intro U0 he.symm
  | @subInherit D Ts0 T' hD hl _ ih =>
    simp only [Ty.cls.injEq] at he
    have ho := Declared.object hwf hD he.1.symm
    exact ih (U0 := Ty.substList (bind D.Delta Ts0) D.Ts) (by simp only [Ty.subst]; rw [ho.1])
  | subInheritLocal hD _ _ =>
    simp only [Ty.cls.injEq] at he
    rcases object_declared hwf with ⟨D0, hD0⟩; exact absurd (Declared.dec_loc hwf hD0.1 hD (by rw [hD0.2.1, he.1])) id
  | subVar => cases he

theorem chain_mem {d : Decls} (hwf : WFDecls d) {Delta : Bounds} : forall (n : Nat) {D : Dec},
    Declared d (.dec D) -> (exists D0, List.Mem D0 (superChain d n D.C) /\ D0.C = Object) ->
    forall {U0 : List Ty} {D' : Dec} {U : List Ty}, Declared d (.dec D') ->
    Sub d Delta (.cls D.C U0) (.cls D'.C U) -> List.Mem D' (superChain d n D.C)
  | 0, D, _, hO, _, _, _, _, _ => by
    rcases hO with ⟨D0, h⟩; simp [superChain] at h
  | n + 1, D, hD, hO, U0, D', U, hD', hs => by
    have hf := findDec_self hwf hD.dec_mem
    by_cases ho : D.C = Object
    . have hsc : superChain d (n + 1) D.C = [D] := by
        simp only [superChain, hf]; simp [ho]
      rw [hsc]
      rw [ho] at hs
      rcases sub_from_object hwf hs with ⟨U', hU⟩
      simp only [Ty.cls.injEq] at hU
      have e := ClassDecl.dec.inj (Declared.unique hwf hD' hD (by show D'.C = D.C; rw [hU.1, ho]))
      rw [e]; exact List.Mem.head _
    . have hsc : superChain d (n + 1) D.C = D :: superChain d n D.C' := by
        simp only [superChain, hf]; simp [ho]
      rw [hsc] at hO |-
      rcases Sub.dec_step hwf hD hs with e | hs2
      . simp only [Ty.cls.injEq] at e
        have e2 := ClassDecl.dec.inj (Declared.unique hwf hD' hD e.1)
        rw [e2]; exact List.Mem.head _
      . rcases Declared.super hwf hD with ⟨D2, hD2⟩
        have hsup := hD2.2
        simp only [ClassDecl.sup] at hsup
        have hs3 := hs2.2
        simp only [Ty.subst] at hs3
        rw [<- hsup] at hs3
        have hO' : exists D0, List.Mem D0 (superChain d n D2.C) /\ D0.C = Object := by
          rcases hO with ⟨D0, h⟩
          refine Exists.intro D0 (And.intro ?_ h.2)
          cases h.1 with
          | head => exact absurd h.2 ho
          | tail _ h' => rw [hsup]; exact h'
        have r := chain_mem hwf n hD2.1 hO' hD' hs3
        rw [hsup] at r
        exact List.Mem.tail _ r

theorem flatMap_disjoint {A B : Type} {f : A -> List B} : forall {l : List A}, (l.flatMap f).Nodup ->
    forall {x y : A} {b : B}, List.Mem x l -> List.Mem y l -> Not (x = y) -> List.Mem b (f x) -> List.Mem b (f y) -> False
  | [], _, _, _, _, hx, _, _, _, _ => by cases hx
  | a :: l, hn, x, y, b, hx, hy, hne, hbx, hby => by
    simp only [List.flatMap_cons] at hn
    have hd := List.nodup_append.mp hn
    have inl : forall {z}, List.Mem z l -> List.Mem b (f z) -> List.Mem b (l.flatMap f) := by
      intro z hz hb
      simp only [listMem_iff, List.mem_flatMap]
      exact Exists.intro z (And.intro hz hb)
    cases hx with
    | head =>
      cases hy with
      | head => exact hne rfl
      | tail _ hy => exact hd.2.2 b hbx b (inl hy hby) rfl
    | tail _ hx =>
      cases hy with
      | head => exact hd.2.2 b hby b (inl hx hbx) rfl
      | tail _ hy => exact flatMap_disjoint hd.2.1 hx hy hne hbx hby

theorem field_class_eq {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D D' : Dec} {f : FieldName}
    {U0 U : List Ty} (hD : Declared d (.dec D)) (hD' : Declared d (.dec D'))
    (hf : List.Mem f (D.Ss.map Slot.f)) (hf' : List.Mem f (D'.Ss.map Slot.f))
    (hs : Sub d Delta (.cls D.C U0) (.cls D'.C U)) : D = D' := by
  have hA9 := hwf.2.2.2.2.2.2.2.2.1.2 D hD.dec_mem
  have hm := chain_mem hwf (d.length + 1) hD hA9 hD' hs
  have hA2 := hwf.2.1 D hD.dec_mem
  by_cases e : D = D'
  . exact e
  . have hm0 : List.Mem D (superChain d (d.length + 1) D.C) := by
      have hf0 := findDec_self hwf hD.dec_mem
      by_cases ho : D.C = Object
      . simp only [superChain, hf0]; simp [ho]
      . simp only [superChain, hf0]; simp [ho]
    exact absurd (flatMap_disjoint hA2 hm0 hm e hf hf') id

theorem sub_self_eq {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} {f : FieldName} {U0 U : List Ty}
    (hD : Declared d (.dec D)) (hf : List.Mem f (D.Ss.map Slot.f)) (hs : Sub d Delta (.cls D.C U0) (.cls D.C U)) :
    U = U0 := by
  rcases Sub.dec_step hwf hD hs with e | hs2
  . simp only [Ty.cls.injEq] at e; exact e.2
  . have ho : Not (D.C = Object) := by
      intro ho
      rcases object_declared hwf with ⟨D0, hD0⟩
      have e := ClassDecl.dec.inj (Declared.unique hwf hD hD0.1 (by show D.C = D0.C; rw [ho, hD0.2.1]))
      rw [e, hD0.2.2.2.2.2.2] at hf
      cases hf
    rcases Declared.super hwf hD with ⟨D2, hD2⟩
    have hsup := hD2.2
    simp only [ClassDecl.sup] at hsup
    have hs3 := hs2.2
    simp only [Ty.subst] at hs3
    rw [<- hsup] at hs3
    have hA9 := hwf.2.2.2.2.2.2.2.2.1.2 D hD.dec_mem
    have hf0 := findDec_self hwf hD.dec_mem
    have hsc : superChain d (d.length + 1) D.C = D :: superChain d d.length D.C' := by
      simp only [superChain, hf0]; simp [ho]
    rw [hsc] at hA9
    have hO' : exists D0, List.Mem D0 (superChain d d.length D2.C) /\ D0.C = Object := by
      rcases hA9 with ⟨D0, h⟩
      refine Exists.intro D0 (And.intro ?_ h.2)
      cases h.1 with
      | head => exact absurd h.2 ho
      | tail _ h' => rw [hsup]; exact h'
    have hm := chain_mem hwf d.length hD2.1 hO' hD hs3
    rw [hsup] at hm
    have hA2 := hwf.2.1 D hD.dec_mem
    rw [hsc] at hA2
    simp only [List.flatMap_cons] at hA2
    have hd := List.nodup_append.mp hA2
    exfalso
    apply hd.2.2 f hf f _ rfl
    simp only [List.mem_flatMap]
    exact Exists.intro D (And.intro hm hf)

theorem superChain_stab {d : Decls} : forall (n : Nat) (C : ClassName),
    (exists D0, List.Mem D0 (superChain d n C) /\ D0.C = Object) -> superChain d (n + 1) C = superChain d n C
  | 0, C, h => by cases h with | intro D0 h => simp [superChain] at h
  | n + 1, C, h => by
    cases hf : findDec d C with
    | none => simp [superChain, hf]
    | some D =>
      have hDC : D.C = C := by
        have := (find_some hf).2
        simpa using this
      by_cases ho : C = Object
      . simp [superChain, ho]
      . have h1 : superChain d (n + 2) C = D :: superChain d (n + 1) D.C' := by simp [superChain, hf, ho]
        have h2 : superChain d (n + 1) C = D :: superChain d n D.C' := by simp [superChain, hf, ho]
        rw [h1, h2]
        rw [h2] at h
        have h' : exists D0, List.Mem D0 (superChain d n D.C') /\ D0.C = Object := by
          rcases h with ⟨D0, hD0⟩
          refine Exists.intro D0 (And.intro ?_ hD0.2)
          cases hD0.1 with
          | head => rw [hDC] at hD0; exact absurd hD0.2 ho
          | tail _ h => exact h
        rw [superChain_stab n D.C' h']

def rank (d : Decls) (C : ClassName) : Nat := (superChain d (d.length + 1) C).length

theorem rank_super {d : Decls} (hwf : WFDecls d) {D : Dec} (hD : Declared d (.dec D)) (ho : Not (D.C = Object)) :
    rank d D.C = rank d D.C' + 1 := by
  have hf := findDec_self hwf hD.dec_mem
  have h1 : superChain d (d.length + 1) D.C = D :: superChain d d.length D.C' := by simp [superChain, hf, ho]
  have hA9 := hwf.2.2.2.2.2.2.2.2.1.2 D hD.dec_mem
  rw [h1] at hA9
  have h' : exists D0, List.Mem D0 (superChain d d.length D.C') /\ D0.C = Object := by
    rcases hA9 with ⟨D0, hD0⟩
    refine Exists.intro D0 (And.intro ?_ hD0.2)
    cases hD0.1 with
    | head => exact absurd hD0.2 ho
    | tail _ h => exact h
  simp only [rank]
  rw [h1, superChain_stab d.length D.C' h']
  simp

theorem rank_sub {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} (hD : Declared d (.dec D))
    {Ts : List Ty} {C2 : ClassName} {U : List Ty} (h : Sub d Delta (.cls D.C Ts) (.cls C2 U)) :
    rank d C2 <= rank d D.C := by
  generalize he : Ty.cls D.C Ts = T at h
  generalize ht : Ty.cls C2 U = T' at h
  induction h generalizing D Ts with
  | subRefl =>
    rw [<- ht] at he
    simp only [Ty.cls.injEq] at he
    rw [he.1]; exact Nat.le_refl _
  | @subInherit D' Ts0' T' hD' hl _ ih =>
    simp only [Ty.cls.injEq] at he
    have e := ClassDecl.dec.inj (Declared.unique hwf hD' hD he.1.symm)
    subst e
    rcases Declared.super hwf hD' with ⟨D'', hD''⟩
    have hsup := hD''.2
    simp only [ClassDecl.sup] at hsup
    have r := ih hD''.1 (Ts := Ty.substList (bind D'.Delta Ts0') D'.Ts) (by simp only [Ty.subst]; rw [hsup]) ht
    rw [hsup] at r
    by_cases ho : D'.C = Object
    . have ho2 := (Declared.object hwf hD' ho).1
      rw [ho2, <- ho] at r
      exact r
    . rw [rank_super hwf hD' ho]; exact Nat.le_succ_of_le r
  | subInheritLocal hD' _ _ =>
    simp only [Ty.cls.injEq] at he
    exact absurd (Declared.dec_loc hwf hD hD' he.1) id
  | subVar => cases he

theorem no_cycle {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} (hD : Declared d (.dec D))
    (ho : Not (D.C = Object)) {Ts U : List Ty}
    (h : Sub d Delta ((Ty.cls D.C' D.Ts).subst (bind D.Delta Ts)) (.cls D.C U)) : False := by
  rcases Declared.super hwf hD with ⟨D'', hD''⟩
  have hsup := hD''.2
  simp only [ClassDecl.sup, Ty.subst] at hsup h
  rw [<- hsup] at h
  have r := rank_sub hwf hD''.1 h
  rw [rank_super hwf hD ho, hsup] at r
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) r)

theorem object_args {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {U0 U : List Ty}
    (h : Sub d Delta (.cls Object U0) (.cls Object U)) : U = U0 \/ U = [] := by
  generalize he : Ty.cls Object U0 = T at h
  generalize ht : Ty.cls Object U = T' at h
  induction h generalizing U0 with
  | subRefl => rw [<- ht] at he; simp only [Ty.cls.injEq] at he; exact Or.inl he.2.symm
  | @subInherit D Ts0 T' hD hl _ ih =>
    simp only [Ty.cls.injEq] at he
    have ho := Declared.object hwf hD he.1.symm
    rcases ih (U0 := Ty.substList (bind D.Delta Ts0) D.Ts) (by simp only [Ty.subst]; rw [ho.1]) ht with e | e
    . right; rw [e, ho.2.1]; rfl
    . exact Or.inr e
  | subInheritLocal hD _ _ =>
    simp only [Ty.cls.injEq] at he
    rcases object_declared hwf with ⟨D0, hD0⟩; exact absurd (Declared.dec_loc hwf hD0.1 hD (by rw [hD0.2.1, he.1])) id
  | subVar => cases he

theorem sub_unique_dec {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {T1 : Ty}
    (h1 : exists D Ts, Declared d (.dec D) /\ T1 = .cls D.C Ts) {C' : ClassName} {U1 : List Ty}
    (hs1 : Sub d Delta T1 (.cls C' U1)) : forall {U2 : List Ty}, Sub d Delta T1 (.cls C' U2) -> U1 = U2 := by
  generalize ht : Ty.cls C' U1 = T' at hs1
  induction hs1 with
  | @subRefl T =>
    intro U2 hs2
    rcases h1 with ⟨D, Ts, h1⟩
    rw [h1.2] at ht hs2
    simp only [Ty.cls.injEq] at ht
    rcases Sub.dec_step hwf h1.1 hs2 with e | hs3
    . simp only [Ty.cls.injEq] at e; rw [ht.2, e.2]
    . have hC : C' = D.C := ht.1
      rw [hC] at hs3
      by_cases ho : D.C = Object
      . have hb := (Declared.object hwf h1.1 ho).2.2.1
        have hU : Ts = [] := by have := hs3.1; rw [hb] at this; cases Ts <;> simp_all
        have hs4 := hs3.2
        simp only [Ty.subst] at hs4
        rw [(Declared.object hwf h1.1 ho).1, (Declared.object hwf h1.1 ho).2.1, ho] at hs4
        simp only [Ty.substList] at hs4
        rw [ht.2, hU]
        rcases object_args hwf hs4 with e | e
        . exact e.symm
        . exact e.symm
      . exact absurd (no_cycle hwf h1.1 ho hs3.2) id
  | @subInherit D Ts0 T' hD hl hs ih =>
    intro U2 hs2
    rcases Sub.dec_step hwf hD hs2 with e | hs3
    . rw [<- ht] at hs
      simp only [Ty.cls.injEq] at e
      have hC : C' = D.C := e.1
      rw [hC] at hs
      by_cases ho : D.C = Object
      . have hb := (Declared.object hwf hD ho).2.2.1
        have hT0 : Ts0 = [] := by rw [hb] at hl; cases Ts0 <;> simp_all
        simp only [Ty.subst] at hs
        rw [(Declared.object hwf hD ho).1, (Declared.object hwf hD ho).2.1, ho] at hs
        simp only [Ty.substList] at hs
        rw [e.2, hT0]
        rcases object_args hwf hs with e2 | e2
        . exact e2
        . exact e2
      . exact absurd (no_cycle hwf hD ho hs) id
    . refine ih ?_ ht hs3.2
      rcases Declared.super hwf hD with ⟨D'', hD''⟩
      refine Exists.intro D'' (Exists.intro (Ty.substList (bind D.Delta Ts0) D.Ts) (And.intro hD''.1 ?_))
      simp only [Ty.subst]
      rw [hD''.2]; rfl
  | subInheritLocal hD _ _ =>
    intro _ _
    rcases h1 with ⟨D, Ts, h1⟩
    simp only [Ty.cls.injEq] at h1
    exact absurd (Declared.dec_loc hwf h1.1 hD h1.2.1.symm) id
  | subVar =>
    simp_all

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
    have hK := Kind.subst hd (Delta' := Delta) (s := bind D.Delta Ts0) (fun b hb => (hka.2 b hb).1)
      (fun b hb => (hka.2 b hb).2) hcls
    exact ih rfl hK
  | @subInheritLocal C1 Fs C' Ts' es Ms Ts1 T' hD hl _ ih =>
    cases hk with
    | @wfClass C9 Ts9 Dl0 Ts0 h1 h2 h3 h4 =>
      rcases h1.loc_declared with h' | h'
      . cases h' with
        | intro D hD' => exact absurd (Declared.dec_loc hwf hD'.1 hD hD'.2.1) id
      . rcases scopeFacts hwf hok h1 with ⟨K', hk'⟩
        have hname : K'.name = C1 := by
          rcases hk'.2.1 with ⟨Us, hUs⟩; simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
        have ek := Declared.unique hwf hk'.1 hD hname
        subst ek
        have sf := hk'.2.2
        have hall : forall F, List.Mem F Fs -> F.isFunnel = true :=
          fun F hF => hwf.2.2.2.2.2.2.2.2.2.2 _ hD.mem F hF
        rcases h' with ⟨Fs2, C2, Ts2, es2, Ms2, Dl, hp⟩
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
    | @newLocal C0 Fs C' Ts' es Ms hD =>
      simp only [Ty.cls.injEq] at hgT
      have hlx := congrArg List.length hgT.2
      simp only [vars, List.length_map] at hlx
      rcases h1.loc_declared with h' | h'
      . cases h' with
        | intro D hD' => exact absurd (Declared.dec_loc hwf hD'.1 hD hD'.2.1) id
      . rcases h' with ⟨Fs2, C2, Ts2, es2, Ms2, Dl, hp⟩
        have ek2 := Declared.unique hwf hp.1 hD rfl
        cases ek2
        have hall : forall F, List.Mem F Fs -> F.isFunnel = true :=
          fun F hF => hwf.2.2.2.2.2.2.2.2.2.2 _ hD.mem F hF
        have e0 := pairing_funnels hp.2 hall
        rw [e0] at h3
        have hd := congrArg List.length hp.2.dom_eq
        simp only [dom, List.length_map] at hd
        rw [h3, hd, hlx]

theorem sub_unique {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {K : ClassDecl} (hk : Declared d K) {Ts : List Ty}
    {C' : ClassName} {U1 U2 : List Ty} (h1 : Sub d Delta (.cls K.name Ts) (.cls C' U1))
    (h2 : Sub d Delta (.cls K.name Ts) (.cls C' U2)) : U1 = U2 := by
  cases K with
  | dec D => exact sub_unique_dec hwf (Exists.intro D (Exists.intro Ts (And.intro hk rfl))) h1 h2
  | newLocal C Fs C0 Ts0 es Ms =>
    rcases Declared.super hwf hk with ⟨D', hD'⟩
    have hsup := hD'.2
    simp only [ClassDecl.sup] at hsup
    have back : forall {U : List Ty}, Sub d Delta ((Ty.cls C0 Ts0).subst (bindF Fs Ts)) (.cls C U) -> False := by
      intro U hs
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
    simp only [Ty.substList, List.cons.injEq, Ty.ftvList, listMem_iff, List.mem_append] at h hX
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
    (hg : Generic d C (.cls C (vars Xs))) : Xs.Nodup /\ exists K, Declared d K /\ K.name = C := by
  generalize hgT : Ty.cls C (vars Xs) = T at hg
  cases hg with
  | @dec D hD =>
    simp only [Ty.cls.injEq] at hgT
    have hx : Xs = dom D.Delta := by
      have := hgT.2
      exact vars_inj this
    refine And.intro ?_ (Exists.intro _ (And.intro hD rfl))
    rw [hx]
    exact hwf.2.2.2.2.1 D.Delta (by
      simp only [listMem_iff, List.mem_append, List.mem_map]
      exact Or.inl (Exists.intro D (And.intro hD.dec_mem rfl)))
  | @newLocal C0 Fs C' Ts' es Ms hD =>
    simp only [Ty.cls.injEq] at hgT
    have hx : Xs = domF Fs := by
      have := hgT.2
      simp only [vars] at this
      exact vars_inj this
    refine And.intro ?_ (Exists.intro _ (And.intro hD rfl))
    rw [hx]
    exact hwf.2.2.2.2.2.1 _ hD.mem

theorem cast_runtime {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {T0 : Ty} {C : ClassName}
    {Ts Ts'' : List Ty} {K1 : ClassDecl} {U1 : List Ty} (hk1d : Declared d K1) (hc : Cast d [] T0 (.cls C Ts))
    (hv : Sub d [] (.cls K1.name U1) T0) (hr : Sub d [] (.cls K1.name U1) (.cls C Ts''))
    (hk : Kind d [] (.cls C Ts)) (hk1 : Kind d [] (.cls K1.name U1)) : Sub d [] (.cls K1.name U1) (.cls C Ts) := by
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
    rcases hg.2 with ⟨K, hk'⟩
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

end Funnelling
