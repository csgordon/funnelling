import Funnelling.Sound.PresEasy

open Funnelling.SoundSimp

namespace Funnelling.High

theorem object_unique {d : Decls} (hwf : WFDecls d) {D : Dec} (hD : Declared d (.dec D)) (hO : D.C = Object) :
    D.C' = Object /\ D.Ts = [] := by
  rcases object_declared hwf with ⟨D0, hD0⟩
  have e := K.dec.inj (Declared.unique hwf hD hD0.1 (by show D.C = D0.C; rw [hO, hD0.2.1]))
  rw [e]
  exact And.intro hD0.2.2.2.1 hD0.2.2.2.2.1

theorem sub_from_object {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {U0 : List Ty} {T : Ty}
    (h : Sub d Delta (.cls Object U0) T) : exists U, T = .cls Object U := by
  generalize he : Ty.cls Object U0 = T0 at h
  induction h generalizing U0 with
  | subRefl => exact Exists.intro U0 he.symm
  | @subInherit D Ts0 T' hD hl _ ih =>
    simp only [Ty.cls.injEq] at he
    have ho := object_unique hwf hD he.1.symm
    exact ih (U0 := Ty.substList (bind D.bounds Ts0) D.Ts) (by simp only [Ty.subst]; rw [ho.1])
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
      have e := K.dec.inj (Declared.unique hwf hD' hD (by show D'.C = D.C; rw [hU.1, ho]))
      rw [e]; exact List.Mem.head _
    . have hsc : superChain d (n + 1) D.C = D :: superChain d n D.C' := by
        simp only [superChain, hf]; simp [ho]
      rw [hsc] at hO |-
      rcases Sub.dec_step hwf hD hs with e | hs2
      . simp only [Ty.cls.injEq] at e
        have e2 := K.dec.inj (Declared.unique hwf hD' hD e.1)
        rw [e2]; exact List.Mem.head _
      . cases Declared.super hwf hD with
        | intro D2 hD2 =>
          have hsup := hD2.2
          simp only [K.sup] at hsup
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
      have e := K.dec.inj (Declared.unique hwf hD hD0.1 (by show D.C = D0.C; rw [ho, hD0.2.1]))
      rw [e, hD0.2.2.2.2.2.2] at hf
      cases hf
    rcases Declared.super hwf hD with ⟨D2, hD2⟩
    have hsup := hD2.2
    simp only [K.sup] at hsup
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

theorem field_typing {d : Decls} {Delta : Bounds} {gamma : Gamma} {s : TSubst} {f : FieldName} {v : Value}
    {T0 : Ty} : forall {Ss : List Slot} {vs1 : List Value},
    TypingSeq d Delta gamma (Value.exprs vs1) (Ty.substList s (Ss.map Slot.T)) ->
    List.Mem (f, v) ((Ss.map Slot.f).zip vs1) -> List.Mem { T := T0, f := f } Ss -> (Ss.map Slot.f).Nodup ->
    Typing d Delta gamma v.expr (T0.subst s)
  | [], _, _, h, _, _ => by cases h
  | _ :: _, [], _, h, _, _ => by cases h
  | S :: Ss, w :: vs1, ht, hm, hS, hn => by
    simp only [Value.exprs, List.map_cons, Ty.substList] at ht
    simp only [List.map_cons, List.zip_cons_cons] at hm
    simp only [List.map_cons, List.nodup_cons] at hn
    cases ht with
    | cons h1 h2 =>
      rcases List.mem_cons.mp hm with e | hm'
      . simp only [Prod.mk.injEq] at e
        rcases List.mem_cons.mp hS with eS | hS'
        . have hT : T0 = S.T := by rw [<- eS]
          rw [e.2, hT]; exact h1
        . rw [e.1] at hS'; exact absurd (List.mem_map_of_mem (f := Slot.f) hS') hn.1
      . rcases List.mem_cons.mp hS with eS | hS'
        . have : S.f = f := by rw [<- eS]
          rw [this] at hn
          exact absurd (List.of_mem_zip hm').1 hn.1
        . exact field_typing h2 hm' hS' hn.2
theorem pres_fieldFound {d : Decls} (hwf : WFDecls d) {D : Dec} {f : FieldName} {Gs : List GTy}
    {vs1 vs : List Value} {v : Value} {T : Ty} (hD : Declared d (.dec D)) (hl : vs1.length = D.Ss.length)
    (hm : List.Mem (f, v) ((D.Ss.map Slot.f).zip vs1))
    (h : Typing d [] [] (.field (Value.new D.C Gs (vs1 ++ vs)).expr f) T) : Typing d [] [] v.expr T := by
  rcases inv_field h rfl with ⟨w, hw⟩
  have vt := value_typing hwf hw.ty
  simp only [typeOf] at vt
  have hsub := vt.1.sub
  have hf : List.Mem f (D.Ss.map Slot.f) := (List.of_mem_zip hm).1
  have hf' : List.Mem f (w.D.Ss.map Slot.f) := List.mem_map_of_mem (f := Slot.f) hw.mem
  have eD := field_class_eq hwf hD hw.decl hf hf' hsub
  have hup := hw.up
  have hmem := hw.mem
  rw [<- eD] at hsub hup hmem
  have eT := sub_self_eq hwf hD hf hsub
  rw [eT] at hup
  have ty := vt.2.1
  simp only [Value.expr] at ty
  rcases inv_new ty rfl with h1 | h1
  . cases object_declared hwf with
    | intro D0 hD0 =>
      have e := K.dec.inj (Declared.unique hwf hD hD0.1 (by show D.C = D0.C; rw [h1.1, hD0.2.1]))
      rw [e, hD0.2.2.2.2.2.2] at hf
      cases hf
  . cases h1 with
    | intro w3 hw3 =>
      have e3 := K.dec.inj (Declared.unique hwf hw3.decl hD hw3.name)
      have hsp := hw3.split
      have hfs := hw3.fields
      rw [e3] at hfs
      rw [exprs_append] at hsp
      have hl2 : (Value.exprs vs1).length = w3.es1.length := by
        rw [hfs.length, substList_length]; simp [Value.exprs_eq_map, hl]
      have ev := (List.append_inj hsp hl2).1
      rw [<- ev] at hfs
      exact hup.typing (field_typing hfs hm hmem (fields_nodup hwf hD.dec_mem))

end Funnelling.High