import Funnelling.Sound.Overriding

open Funnelling.SoundSimp

namespace Funnelling

theorem value_new_declared {d : Decls} (hwf : WFDecls d) {C : ClassName} {Gs : List GTy} {vs : List Value} {T : Ty}
    (h : Typing d [] [] (Value.new C Gs vs).expr T) : exists D, Declared d (.dec D) /\ D.C = C := by
  rcases inv_new h rfl with h1 | h1
  . cases object_declared hwf with
    | intro D hD => exact Exists.intro D (And.intro hD.1 (by rw [hD.2.1, h1.1]))
  . cases h1 with
    | intro w hw => exact Exists.intro w.D (And.intro hw.decl hw.name)

theorem pres_ifElse {d : Decls} {v : Value} {T0 : Ty} {x : VarName} {e1 e2 : Expr} {T : Ty}
    (h : Typing d [] [] (.ifInst v.expr T0 x e1 e2) T) : Typing d [] [] e2 T := by
  rcases inv_if h rfl with ⟨w, hw⟩; exact hw.up.typing hw.ty2

theorem pres_addSuper {d : Decls} (hwf : WFDecls d) {C : ClassName} {m : MethName} {v : Value}
    {Gs Gs' : List GTy} {vs0 vs : List Value} {T : Ty} (hv : v = Value.new C Gs vs0)
    (h : Typing d [] [] (.call v.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] (.superCall v.expr (.cls C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T := by
  rcases inv_call h rfl with ⟨w, hw⟩
  have vt := value_typing hwf hw.ty0
  subst hv
  rcases value_new_declared hwf vt.2.1 with ⟨D, hD⟩
  have hn := hD.2
  subst hn
  have hsub := vt.1.sub
  rcases Sub.top_target hwf hD.1 hsub with ⟨D0, hD0⟩
  have hc := hD0.2
  have hscope := hw.scope
  have hmeth := hw.meth
  rw [<- hc] at hsub hscope hmeth
  have e := Scope.dec_eq hwf hD0.1 hscope
  have hsig := hw.sig
  have hsubs := hw.subs
  have hlen2 := hw.len2
  rw [e.1, e.2] at hsig hsubs hlen2
  have vt2 := vt.2.1
  have vk := vt.2.2
  exact hw.up.typing (Typing.callLbRuntime hsub hD0.1 hmeth hlen2 hw.len1 hsig hD.1 vk hw.kinds hsubs
    (TypingSeq.cons vt2 hw.args))

theorem gtys_length {Gs : List GTy} : (GTy.tys Gs).length = Gs.length := by rw [GTy.tys_eq_map]; simp

theorem pres_searchSuper {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {D : Dec}
    {m : MethName} {v : Value} {Gs Gs' : List GTy} {vs : List Value} {T : Ty} (hD : Declared d (.dec D))
    (hm : Not (List.Mem m (D.Ms.map Method.name))) (hG : Gs.length = D.bounds.length)
    (h : Typing d [] [] (.superCall v.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] (.superCall v.expr (.cls D.C' (Ty.substList (bind D.bounds (GTy.tys Gs)) D.Ts))
      (GTy.tys Gs') m (Value.exprs vs)) T := by
  rcases inv_super h rfl with ⟨w, hw⟩
  have ha := hw.ann
  simp only [Ty.cls.injEq] at ha
  have eD := K.dec.inj (Declared.unique hwf hw.decl hD ha.1.symm)
  have hsub := hw.sub
  have hargs := hw.args
  have hkind := hw.kind
  rw [eD, <- ha.2] at hsub hargs hkind
  have hM := MethodIn.dec hwf hw.decl0 hw.meth
  rcases Sub.dec_step hwf hD hsub with e | hs
  . simp only [Ty.cls.injEq] at e
    have e0 := K.dec.inj (Declared.unique hwf hw.decl0 hD e.1)
    rw [e0] at hM
    exact absurd (List.mem_map_of_mem (f := Method.name) hM) hm
  . rcases Declared.super hwf hD with ⟨D', hD'⟩
    have hsup := hD'.2
    simp only [K.sup] at hsup
    have hcls := (hok D hD.dec_mem).2.1 _ (List.Mem.head _)
    have hka := kind_dec_args hwf hD hkind
    have hK := Kind.subst hd (Delta' := []) (s := bind D.bounds (GTy.tys Gs)) (fun b hb => (hka.2 b hb).1)
      (fun b hb => (hka.2 b hb).2) hcls
    rw [<- hsup] at hK hs |-
    cases hargs with
    | cons hv hrest =>
      have hv' := Typing.subs hv hK (Sub.subInherit hD (by rw [gtys_length, hG])
        (by simp only [Ty.subst]; rw [<- hsup]; exact Sub.subRefl))
      exact hw.up.typing (Typing.callLbRuntime hs.2 hw.decl0 hw.meth hw.len0 hw.len1 hw.sig hD'.1 hK
        hw.kinds hw.subs (TypingSeq.cons hv' hrest))

theorem pres_innerSuper {d : Decls} (hwf : WFDecls d) {C C' : ClassName} {Ms : List Method} {m : MethName}
    {v0 : Value} {Gs0 Gs Gs' : List GTy} {vs0 vs : List Value} {T : Ty}
    (hv : v0 = Value.newLocal C Gs0 C' Gs vs0 Ms) (hm : Not (List.Mem m (Ms.map Method.name)))
    (h : Typing d [] [] (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] (.superCall v0.expr (.cls C' (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T := by
  rcases inv_call h rfl with ⟨w, hw⟩
  have vt := value_typing hwf hw.ty0
  subst hv
  have ty0 := hw.ty0
  rcases inv_local ty0 rfl with ⟨w2, hw2⟩
  rcases consistent_unfold hw2.cons with ⟨Fs', Ts', es', Ms', hc⟩
  have hDl := hc.1
  have hup := hw2.up
  rw [abs_ground] at hup
  have hne : Not (w.C0 = C) := by
    intro e
    have hM := MethodIn.loc hwf hDl (by rw [<- e]; exact hw.meth)
    exact hm ((hc.2.2.2.1 m).mp (List.mem_map_of_mem (f := Method.name) hM))
  have hsub : Sub d [] (.cls C (GTy.tys Gs0)) (.cls w.C0 w.Ts0) := by
    rcases hup with e | hs
    . simp only [Ty.cls.injEq] at e; exact absurd e.1.symm hne
    . exact hs.1
  rcases Sub.loc_step hwf hDl hsub with e | hs2
  . simp only [Ty.cls.injEq] at e; exact absurd e.1 hne
  . have hts := hc.2.2.1
    rw [abs_ground] at hts
    have hs3 := hs2.2
    simp only [Ty.subst] at hs3
    rw [<- hts] at hs3
    rcases Declared.super hwf hDl with ⟨D', hD'⟩
    have hsup := hD'.2
    simp only [K.sup] at hsup
    rw [<- hsup] at hs3
    rcases Sub.top_target hwf hD'.1 hs3 with ⟨D0, hD0⟩
    have hcC := hD0.2
    have hscope := hw.scope
    have hmeth := hw.meth
    rw [<- hcC] at hs3 hscope hmeth
    have e := Scope.dec_eq hwf hD0.1 hscope
    have hsig := hw.sig
    have hsubs := hw.subs
    have hlen2 := hw.len2
    rw [e.1, e.2] at hsig hsubs hlen2
    have hK := hw2.kindS
    rw [pairing_ground_nil hw2.pair] at hK
    rw [<- hsup] at hK
    have hv0 := vt.2.1
    have hv1 := Typing.subs hv0 hK (Sub.subInheritLocal hDl hs2.1
      (by simp only [Ty.subst]; rw [<- hts, <- hsup]; exact Sub.subRefl))
    have hres := Typing.callLbRuntime hs3 hD0.1 hmeth hlen2 hw.len1 hsig hD'.1 hK hw.kinds hsubs
      (TypingSeq.cons hv1 hw.args)
    rw [hsup] at hres
    exact hw.up.typing hres

theorem typing_new_exact {d : Decls} {Delta : Bounds} {gamma : Gamma} {C : ClassName} {Ts : List Ty}
    {es : List Expr} {T : Ty} (h : Typing d Delta gamma (.new C Ts es) T) :
    Typing d Delta gamma (.new C Ts es) (.cls C Ts) := by
  rcases inv_new h rfl with h1 | h1
  . rw [h1.1, h1.2.1, h1.2.2.1]; exact Typing.newObject
  . rcases h1 with ⟨w, hw⟩
    rw [<- hw.name, hw.split]
    exact Typing.newTop hw.decl hw.kind hw.len hw.fields hw.sup

theorem TypingSeq.length {d : Decls} {Delta : Bounds} {gamma : Gamma} {es : List Expr} {Ts : List Ty}
    (h : TypingSeq d Delta gamma es Ts) : es.length = Ts.length := by
  induction es generalizing Ts with
  | nil => cases h; rfl
  | cons e es ih => cases h with | cons _ h2 => simp [ih h2]

theorem pres_innerFieldSuper {d : Decls} (hwf : WFDecls d) {C C' : ClassName} {Ms : List Method} {f : FieldName}
    {Gs Gs' : List GTy} {vs : List Value} {T : Ty}
    (h : Typing d [] [] (.field (Value.newLocal C Gs C' Gs' vs Ms).expr f) T) :
    Typing d [] [] (.field (Value.new C' Gs' vs).expr f) T := by
  rcases inv_field h rfl with ⟨w, hw⟩
  have ty := hw.ty
  rcases inv_local ty rfl with ⟨w2, hw2⟩
  rcases consistent_unfold hw2.cons with ⟨Fs', Ts', es', Ms', hc⟩
  have hDl := hc.1
  have hup := hw2.up
  rw [abs_ground] at hup
  have hne : Not (w.D.C = C) := fun e => Declared.dec_loc hwf hw.decl hDl e
  rcases hup with e | hs
  . simp only [Ty.cls.injEq] at e; exact absurd e.1.symm hne
  . rcases Sub.loc_step hwf hDl hs.1 with e | hs2
    . simp only [Ty.cls.injEq] at e; exact absurd e.1 hne
    . have hts := hc.2.2.1
      rw [abs_ground] at hts
      have hs3 := hs2.2
      simp only [Ty.subst] at hs3
      rw [<- hts] at hs3
      have hnew := typing_new_exact hw2.tyNew
      exact hw.up.typing (Typing.declField (Typing.subs hnew hs.2 hs3) hw.decl hw.mem hw.len)

theorem exprs_append {vs1 vs : List Value} : Value.exprs (vs1 ++ vs) = Value.exprs vs1 ++ Value.exprs vs := by
  simp [Value.exprs_eq_map]

theorem pres_simpleFieldSuper {d : Decls} (hwf : WFDecls d) {D : Dec} {f : FieldName} {Gs : List GTy}
    {vs1 vs : List Value} {T : Ty} (hD : Declared d (.dec D)) (hl : vs1.length = D.Ss.length)
    (hf : Not (List.Mem f (D.Ss.map Slot.f))) (hO : Not (D.C = Object))
    (h : Typing d [] [] (.field (Value.new D.C Gs (vs1 ++ vs)).expr f) T) :
    Typing d [] [] (.field (.new D.C' (Ty.substList (bind D.bounds (GTy.tys Gs)) D.Ts) (Value.exprs vs)) f) T := by
  rcases inv_field h rfl with ⟨w, hw⟩
  have vt := value_typing hwf hw.ty
  simp only [typeOf] at vt
  have hne : Not (w.D = D) := by
    intro e
    have hm := hw.mem
    rw [e] at hm
    exact hf (List.mem_map_of_mem (f := Slot.f) hm)
  rcases vt.1 with e | hs
  . simp only [Ty.cls.injEq] at e
    exact absurd (K.dec.inj (Declared.unique hwf hw.decl hD e.1.symm)) hne
  . rcases Sub.dec_step hwf hD hs.1 with e | hs2
    . simp only [Ty.cls.injEq] at e
      exact absurd (K.dec.inj (Declared.unique hwf hw.decl hD e.1)) hne
    . have ty := vt.2.1
      rcases inv_new ty rfl with h1 | h1
      . exact absurd h1.1 hO
      . rcases h1 with ⟨w3, hw3⟩
        have e3 := K.dec.inj (Declared.unique hwf hw3.decl hD hw3.name)
        have hsp := hw3.split
        have hsup := hw3.sup
        have hfl := hw3.fields.length
        rw [e3] at hsup hfl
        rw [exprs_append] at hsp
        have hl2 : (Value.exprs vs1).length = w3.es1.length := by
          rw [hfl, substList_length]; simp [Value.exprs_eq_map, hl]
        have ev := (List.append_inj hsp hl2).2
        rw [<- ev] at hsup
        have hnew := typing_new_exact hsup
        have hs3 := hs2.2
        exact hw.up.typing (Typing.declField (Typing.subs hnew hs.2 hs3) hw.decl hw.mem hw.len)

theorem field_typing {d : Decls} {Delta : Bounds} {gamma : Gamma} {s : TSubst} {f : FieldName} {v : Value}
    {T0 : Ty} : forall {Ss : List Slot} {vs1 : List Value},
    TypingSeq d Delta gamma (Value.exprs vs1) (Ty.substList s (Ss.map Slot.T)) ->
    List.Mem (f, v) ((Ss.map Slot.f).zip vs1) -> List.Mem { T := T0, f := f } Ss -> (Ss.map Slot.f).Nodup ->
    Typing d Delta gamma v.expr (T0.subst s)
  | [], _, _, h, _, _ => by cases h
  | _ :: _, [], _, h, _, _ => by cases h
  | S :: Ss, w :: vs1, ht, hm, hS, hn => by
    simp only [Value.exprs, List.map_cons, Ty.substList, List.zip_cons_cons, List.nodup_cons] at ht hm hn
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
  . rcases object_declared hwf with ⟨D0, hD0⟩
    have e := K.dec.inj (Declared.unique hwf hD hD0.1 (by show D.C = D0.C; rw [h1.1, hD0.2.1]))
    rw [e, hD0.2.2.2.2.2.2] at hf
    cases hf
  . rcases h1 with ⟨w3, hw3⟩
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
    exact Expr.noShadow_scope h hs
  | .new _ _ es, _, _, _, h, hs => Expr.noShadowList_scope h hs
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
    rcases inv_local h rfl with ⟨w, hw⟩
    rcases consistent_unfold hw.cons with ⟨Fs', Ts', es', Ms', h⟩
    exact Exists.intro _ (Exists.intro (GTy.tys Gs) (And.intro h.1 (by simp [typeOf, K.name])))

theorem pres_ifThen {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {C' : ClassName}
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
  rcases value_declared hwf vt.2.1 with ⟨k, U, hU⟩
  have hk1 := vt.2.2
  rw [hU.2] at hsv hs hk1
  have hc := cast_runtime hwf hok hd hU.1 hw.cast hsv hs hw.kind hk1
  rw [<- hU.2] at hc
  have hvT : Typing d [] [] v.expr (.cls C' Ts) := Typing.subs vt.2.1 hw.kind hc
  have hn := ha.2.2.2.2.1
  simp only [Expr.noShadow, Bool.and_eq_true] at hn
  have hu := WFExpr.uniq ha
  have ht := WFExpr.noThis ha
  simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht
  have hn' : e1'.noShadow [] [x] = true :=
    Expr.noShadow_scope ((Expr.vsubst_back _ _).2.2 _ _ ha'.2.2.2.2.1)
      (fun y hy hm => absurd hm (hdf y hy))
  have ht' : NoThis e1' := noThis_of_vsubst (WFExpr.noThis ha')
  have hu' : e1'.uniq := (Expr.vsubst_back _ _).2.1 (WFExpr.uniq ha')
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

mutual
theorem Expr.noShadow_tscope : forall {e : Expr} {Xs Xs2 : List TVarName} {xs : List VarName},
    e.noShadow Xs xs = true -> (forall X, List.Mem X e.tbinders -> List.Mem X Xs2 -> List.Mem X Xs) ->
    e.noShadow Xs2 xs = true
  | .var _, _, _, _, _, _ => rfl
  | .call e _ _ es, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
  | .superCall e _ _ _ es, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
  | .field e _, _, _, _, h, hs => by
    simp only [Expr.noShadow] at h |-
    exact Expr.noShadow_tscope h hs
  | .new _ _ es, _, _, _, h, hs => Expr.noShadowList_tscope h hs
  | .newLocal _ _ _ _ es Ms, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadowList_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Method.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
  | .ifInst e0 _ _ e1 e2, _, _, _, h, hs => by
    simp only [Expr.noShadow, Bool.and_eq_true] at h |-
    simp only [Expr.tbinders, listMem_iff, List.mem_append] at hs
    exact And.intro (And.intro (And.intro (Expr.noShadow_tscope h.1.1.1 (fun y hy => hs y (Or.inl (Or.inl hy))))
      h.1.1.2) (Expr.noShadow_tscope h.1.2 (fun y hy => hs y (Or.inl (Or.inr hy)))))
      (Expr.noShadow_tscope h.2 (fun y hy => hs y (Or.inr hy)))
theorem Expr.noShadowList_tscope : forall {es : List Expr} {Xs Xs2 : List TVarName} {xs : List VarName},
    Expr.noShadowList Xs xs es = true -> (forall X, List.Mem X (Expr.tbindersList es) -> List.Mem X Xs2 -> List.Mem X Xs) ->
    Expr.noShadowList Xs2 xs es = true
  | [], _, _, _, _, _ => rfl
  | e :: es, _, _, _, h, hs => by
    simp only [Expr.noShadowList, Bool.and_eq_true] at h |-
    simp only [Expr.tbindersList, listMem_iff, List.mem_append] at hs
    exact And.intro (Expr.noShadow_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Expr.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
theorem Method.noShadow_tscope : forall {M : Method} {Xs Xs2 : List TVarName} {xs : List VarName},
    M.noShadow Xs xs = true -> (forall X, List.Mem X M.tbinders -> List.Mem X Xs2 -> List.Mem X Xs) ->
    M.noShadow Xs2 xs = true
  | .mk Dl _ _ ps e, Xs, Xs2, _, h, hs => by
    simp only [Method.noShadow, Bool.and_eq_true] at h |-
    simp only [Method.tbinders, listMem_iff, List.mem_append] at hs
    refine And.intro (And.intro (all_not_contains_of (fun X hX hm =>
      not_mem_of_all_not_contains h.1.1 hX (hs X (Or.inl hX) hm))) h.1.2) ?_
    refine Expr.noShadow_tscope h.2 (fun y hy hm => ?_)
    simp only [listMem_iff, List.mem_append] at hm |-
    rcases hm with hm | hm
    . exact Or.inl (hs y (Or.inr hy) hm)
    . exact Or.inr hm
theorem Method.noShadowList_tscope : forall {Ms : List Method} {Xs Xs2 : List TVarName} {xs : List VarName},
    Method.noShadowList Xs xs Ms = true ->
    (forall X, List.Mem X (Method.tbindersList Ms) -> List.Mem X Xs2 -> List.Mem X Xs) ->
    Method.noShadowList Xs2 xs Ms = true
  | [], _, _, _, _, _ => rfl
  | M :: Ms, _, _, _, h, hs => by
    simp only [Method.noShadowList, Bool.and_eq_true] at h |-
    simp only [Method.tbindersList, listMem_iff, List.mem_append] at hs
    exact And.intro (Method.noShadow_tscope h.1 (fun y hy => hs y (Or.inl hy)))
      (Method.noShadowList_tscope h.2 (fun y hy => hs y (Or.inr hy)))
end

theorem typingSeq_lookup {d : Decls} : forall {g : Gamma} {vs : List Value},
    (gdom g).Nodup -> TypingSeq d [] [] (Value.exprs vs) (g.map VarDecl.T) ->
    forall x v U, List.lookup x ((gdom g).zip vs) = some v -> g.lookup x = some U -> Typing d [] [] v.expr U
  | [], _, _, _, x, v, U, _, h => by simp [Gamma.lookup] at h
  | _ :: _, [], _, h, _, _, _, _, _ => by cases h
  | y :: g, v0 :: vs, hn, h, x, v, U, h1, h2 => by
    cases h with
    | cons ht hts =>
      simp only [gdom, List.map_cons, List.zip_cons_cons] at h1 hn
      by_cases e : x = y.x
      . subst e
        rw [lookup_cons_eq] at h1
        cases h1
        simp only [Gamma.lookup, List.find?_cons, beq_self_eq_true, Option.map_some] at h2
        cases h2
        exact ht
      . rw [lookup_cons_ne e] at h1
        have hb : (y.x == x) = false := by simpa using fun h => e h.symm
        simp only [Gamma.lookup, List.find?_cons, hb] at h2
        exact typingSeq_lookup (List.nodup_cons.mp hn).2 hts x v U h1 h2

theorem gsubst_ty_bind {Dl : Bounds} {Gs : List GTy} : GSubst.ty (bind Dl Gs) = bind Dl (GTy.tys Gs) := by
  rw [GTy.tys_eq_map]
  simp only [GSubst.ty, bind, List.zip_map_right]
  rfl

theorem exprs_mem {v : Value} : forall {vs : List Value}, List.Mem v vs -> List.Mem v.expr (Value.exprs vs)
  | _, .head _ => by simp only [Value.exprs]; exact List.Mem.head _
  | _, .tail _ h => by simp only [Value.exprs]; exact List.Mem.tail _ (exprs_mem h)

theorem uniqList_mem_e {e : Expr} : forall {es : List Expr}, List.Mem e es -> Expr.uniqList es -> e.uniq
  | _, .head _, hu => by simp only [Expr.uniqList] at hu; exact hu.1
  | _, .tail _ h, hu => by simp only [Expr.uniqList] at hu; exact uniqList_mem_e h hu.2

theorem vbindersList_mem_e {e : Expr} {x : VarName} : forall {es : List Expr}, List.Mem e es ->
    List.Mem x e.vbinders -> List.Mem x (Expr.vbindersList es)
  | _, .head _, hx => by simp only [Expr.vbindersList, listMem_iff, List.mem_append]; exact Or.inl hx
  | _, .tail _ h, hx => by simp only [Expr.vbindersList, listMem_iff, List.mem_append]; exact Or.inr (vbindersList_mem_e h hx)

theorem found_tail {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {B : Bounds} {Gall : List GTy}
    {Tt T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value} {vs : List Value}
    (hb : Typing d B ([{ T := Tt, x := this }] ++ ps) e0 T0) (hgok : GOk d B (bind B Gall))
    (hfst : (bind B Gall).map Prod.fst = dom B) (hN' : (this :: ps.map VarDecl.x).Nodup) (hp : ps.length = vs.length)
    (hgs : GSubstDefined (dom B) e0) (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0)
    (hnx : e0.noShadow [] (this :: ps.map VarDecl.x) = true) (ht0 : NoThis e0) (hu0 : e0.uniq)
    (ha' : WFExpr ((e0.gsubst (bind B Gall)).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))))
    (hargs : TypingSeq d [] [] (Value.exprs (v0 :: vs)) (Ty.substList (GSubst.ty (bind B Gall)) (Tt :: ps.map VarDecl.T)))
    (hn : Expr.noShadowList [] [] (Value.exprs (v0 :: vs)) = true)
    (ht : Not (List.Mem this (Expr.vbindersList (Value.exprs (v0 :: vs))))) (hu : Expr.uniqList (Value.exprs (v0 :: vs))) :
    Typing d [] [] ((e0.gsubst (bind B Gall)).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs)))
      (T0.subst (GSubst.ty (bind B Gall))) := by
  have hgt := Typing.gsub hwf hok hd hb (s := bind B Gall) (Xs := []) (xs := this :: ps.map VarDecl.x) hgok
    (fun X hX hm => hgs X hX (by rw [hfst] at hm; exact hm)) (by simpa [gdom] using hN')
    (fun y hy => by simpa [gdom] using hy) hnx ht0 hu0
  have eB : gsubB (bind B Gall) B = [] := by
    simp only [gsubB, Bounds.subst]
    rw [List.filter_eq_nil_iff.mpr]
    . rfl
    . intro b hb
      rw [hfst]
      have hc : (dom B).contains b.X = true := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := Bound.X) hb)
      rw [hc]; decide
  rw [eB] at hgt
  have hgd : gdom (gsubG (bind B Gall) ([{ T := Tt, x := this }] ++ ps)) = this :: ps.map VarDecl.x := by
    rw [gdom_gsubG]; simp [gdom]
  have hg1T : (gsubG (bind B Gall) ([{ T := Tt, x := this }] ++ ps)).map VarDecl.T =
      Ty.substList (GSubst.ty (bind B Gall)) (Tt :: ps.map VarDecl.T) := by
    simp only [gsubG, List.singleton_append, List.map_cons, VarDecl.subst, Ty.substList]
    rw [params_T_subst]
  have hnf : ((this :: ps.map VarDecl.x).zip (v0 :: vs)).map Prod.fst = this :: ps.map VarDecl.x :=
    zip_map_fst (by simp [hp])
  have eG : gsub ((this :: ps.map VarDecl.x).zip (v0 :: vs)) (gsubG (bind B Gall) ([{ T := Tt, x := this }] ++ ps)) =
      [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hax : List.Mem a.x (gdom (gsubG (bind B Gall) ([{ T := Tt, x := this }] ++ ps))) :=
      List.mem_map_of_mem (f := VarDecl.x) ha
    rw [hgd, <- hnf] at hax
    have hc := List.contains_iff_mem.mpr hax
    show Not ((!(List.contains _ a.x)) = true)
    rw [hc]; decide
  have hres := Typing.vsub hgt (n := (this :: ps.map VarDecl.x).zip (v0 :: vs)) (Xs := [])
    (xs := this :: ps.map VarDecl.x) (xs' := [])
    (fun x v U h1 h2 => typingSeq_lookup (vs := v0 :: vs) (by rw [hgd]; exact hN') (by rw [hg1T]; exact hargs) x v U
      (by rw [hgd]; exact h1) h2)
    (fun p hp => by
      have hv := exprs_mem (List.of_mem_zip hp).2
      exact And.intro (noShadowList_mem hv hn) (And.intro (fun h => ht (vbindersList_mem_e hv h)) (uniqList_mem_e hv hu)))
    (fun y hy => by rw [hnf]; rw [Expr.vbinders_gsubst] at hy; exact hvs y hy)
    (by rw [hgd]; exact hN')
    (by rw [hgd]; exact fun y hy => hy)
    (by rw [eG]; intro y hy; cases hy)
    (by rw [Expr.noShadow_gsubst]; exact hnx) ha'.2.2.2.2.1
    (by simpa [NoThis, Expr.vbinders_gsubst] using ht0) (by rw [Expr.uniq_gsubst]; exact hu0)
  rwa [eG] at hres

theorem found_body {e0 : Expr} {s : GSubst} {n : VSubst} {Xs : List TVarName} {Delta' : Bounds} {T0 : Ty}
    {m : MethName} {ps : List VarDecl} (ha' : WFExpr ((e0.gsubst s).vsubst n))
    (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0) (hgs : GSubstDefined (Xs ++ dom Delta') e0)
    (hN : (dom Delta').Nodup) (hN' : (this :: ps.map VarDecl.x).Nodup) :
    e0.noShadow [] (this :: ps.map VarDecl.x) = true /\ NoThis e0 /\ e0.uniq /\
    (Method.mk Delta' T0 m ps e0).noShadow [] [] = true /\ NoThisM (Method.mk Delta' T0 m ps e0) /\
    (Method.mk Delta' T0 m ps e0).uniq := by
  have hn0 := (Expr.vsubst_back _ _).2.2 _ _ ha'.2.2.2.2.1
  rw [Expr.noShadow_gsubst] at hn0
  have hnx : e0.noShadow [] (this :: ps.map VarDecl.x) = true :=
    Expr.noShadow_scope hn0 (fun y hy hm => absurd hm (hvs y hy))
  have ht0 : NoThis e0 := by
    have := noThis_of_vsubst (WFExpr.noThis ha')
    simpa [NoThis, Expr.vbinders_gsubst] using this
  have hu0 : e0.uniq := by
    have := (Expr.vsubst_back _ _).2.1 (WFExpr.uniq ha')
    rwa [Expr.uniq_gsubst] at this
  have hnD : e0.noShadow (dom Delta') (this :: ps.map VarDecl.x) = true :=
    Expr.noShadow_tscope hnx (fun X hX hm => absurd (by simp only [listMem_iff, List.mem_append] at hm |-; exact Or.inr hm)
      (hgs X hX))
  refine ⟨hnx, ht0, hu0, ?_, ?_, And.intro hN (And.intro (List.nodup_cons.mp hN').2 hu0)⟩
  . simp only [Method.noShadow, List.nil_append, List.cons_append, Bool.and_eq_true]
    exact And.intro (And.intro (by simp) (by simp)) hnD
  . simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or]
    exact And.intro (List.nodup_cons.mp hN').1 ht0

theorem pres_simpleFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {D : Dec} {M : Method}
    {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr} {v0 : Value} {Gs Gs' : List GTy}
    {vs : List Value} {T : Ty} (hD : Declared d (.dec D)) (hM : List.Mem M D.Ms)
    (hF : FreshM M (.mk Delta' T0 m ps e0)) (hG : Gs.length = D.bounds.length) (hG' : Gs'.length = Delta'.length)
    (hN : (dom D.bounds ++ dom Delta').Nodup) (hN' : (this :: ps.map VarDecl.x).Nodup)
    (hp : ps.length = vs.length) (hgs : GSubstDefined (dom D.bounds ++ dom Delta') e0)
    (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0)
    (ha : WFExpr (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)))
    (ha' : WFExpr ((e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
      ((this :: ps.map VarDecl.x).zip (v0 :: vs))))
    (h : Typing d [] [] (.superCall v0.expr (.cls D.C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
      ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  have hwm := WFDecls.method hwf hD.dec_mem hM
  rcases found_body (T0 := T0) (m := m) ha' hvs hgs (nodup_append_right hN) hN' with ⟨hnx, ht0, hu0, hnM', htM', huM'⟩
  rcases inv_super h rfl with ⟨⟨D1, Ts, D0, Ts0, Delta1, T0o, pso, body, T0', Ts'⟩, hw⟩
  have ann := hw.ann
  simp only [Ty.cls.injEq] at ann
  have eD : D = D1 := by
    have e := Declared.unique hwf hD hw.decl (by simp only [K.name]; exact ann.1)
    injection e
  subst eD
  have eTs := ann.2
  subst eTs
  rcases hw.meth with ⟨k, hk, hkn, hkM⟩
  have ek := Declared.unique hwf hk hw.decl0 hkn
  subst ek
  rcases dec_override hwf hok hd hD hM hw.decl0 (by rw [gtys_length]; exact hG) hw.sub with ⟨Us, hUs, hO, hUf⟩
  have hO' := OverrideOkM.ren (rv := []) (rt := []) hwf hok hO hF.1
    (fun X hX hm => Method.noShadow_dom hwm.2.2 X hm (hUf X hX)) hwm.1
  rw [Ty.renList_id (fun _ _ => rn_nil)] at hO'
  generalize hTT : Ty.cls D0.C Us = TT at hO'
  cases hO' with
  | absent h1 h2 =>
    simp only [Ty.cls.injEq] at hTT
    have e := Declared.unique hwf hw.decl0 h1 (by simp only [K.name]; exact hTT.1)
    cases e
    exact absurd (List.mem_map_of_mem (f := Method.name) hkM) h2
  | loc h1 =>
    simp only [Ty.cls.injEq] at hTT
    exact absurd (Declared.dec_loc hwf hw.decl0 h1 hTT.1) id
  | @dec D2 Us2 _ _ _ _ _ Do T0x psx ex h1 h2 h3 h4 h5 h6 =>
    simp only [Ty.cls.injEq] at hTT
    have e := Declared.unique hwf hw.decl0 h1 (by simp only [K.name]; exact hTT.1)
    cases e
    have eU := hTT.2
    subst eU
    have eM := names_unique (Declared.namesNodup hwf hw.decl0) h2 hkM rfl
    simp only [Method.mk.injEq] at eM
    rcases eM with ⟨eM1, eM2, _, eM4, _⟩
    subst eM1 eM2 eM4
    have hsg : GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs')) =
        (dom D.bounds ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs') := by
      rw [gsubst_ty_bind, GTy.tys_eq_map, GTy.tys_eq_map, GTy.tys_eq_map, List.map_append]
      simp only [bind, dom_append]
    have hlenF : (GTy.tys Gs ++ GTy.tys Gs').length = (dom D.bounds ++ dom Delta').length := by
      simp [gtys_length, hG, hG', dom]
    have hvF := vars_subst hN hlenF
    rw [<- hsg, vars_append, substList_app] at hvF
    have hv1 := List.append_inj hvF (by simp [substList_length, vars, dom, gtys_length, hG])
    have hcomp1 : forall L, (forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom D.bounds)) ->
        Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) L =
          Ty.substList (bind D.bounds (GTy.tys Gs)) L := by
      intro L hL
      conv => lhs; rw [<- substList_bind_vars_id hL]
      rw [substList_bind_comp (by simp [vars, dom]) hL, hv1.1]
    have hUt : Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) Us = Ts0 := by
      rw [hcomp1 Us hUf]; exact hUs.symm
    have hcl0 := declMeth_closed hwf hok hw.decl0 hkM
    simp only [K.gvars, <- dom_append] at hcl0
    have hlen0 : (Us ++ vars (dom Delta')).length = (D0.bounds ++ Do).length := by simp [h3, h4, vars, dom]
    have hcomp2 : forall L, (forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom (D0.bounds ++ Do))) ->
        Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs')))
          (Ty.substList (bind (D0.bounds ++ Do) (Us ++ vars (dom Delta'))) L) =
          Ty.substList (bind (D0.bounds ++ Do) (Ts0 ++ GTy.tys Gs')) L := by
      intro L hL
      rw [substList_bind_comp hlen0 hL, substList_app, hUt, hv1.2]
    have hsig : Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) (T0 :: ps.map VarDecl.T) =
        T0' :: Ts' := by
      rw [<- h6, hcomp2 _ hcl0.2]; exact hw.sig.symm
    have hcod : Ty.substList (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) (cod Delta') =
        Ty.substList (bind (D0.bounds ++ Do) (Ts0 ++ GTy.tys Gs')) (cod Do) := by
      rw [<- h5, hcomp2 _ hcl0.1]
    have hmo := (hok D hD.dec_mem).2.2.1 M hM
    have env : REnv [] [] D.bounds D.bounds [{ T := .cls D.C (vars (dom D.bounds)), x := this }]
        [{ T := .cls D.C (vars (dom D.bounds)), x := this }] (dom D.bounds) [this] [this] :=
      { bD := fun b hb => by rw [rn_nil, Ty.ren_id (fun _ _ => rn_nil)]; exact hb
        dX := fun X hX => hX
        dT := fun b hb X hX => Kind.ftv ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb)) X hX
        g := fun z U hl => by rw [rn_nil, Ty.ren_id (fun _ _ => rn_nil)]; exact hl
        gT := fun y hy X hX => by
          cases hy with
          | head => exact ftv_vars (by simpa [Ty.ftv] using hX)
          | tail _ h => cases h
        gN := by simp [gdom]
        gx := fun y hy => hy
        gx' := fun y hy => hy
        kv := fun _ h => by cases h }
    have hmo' := MethodOk.ren hwf hok hd hmo hF.1 env hwm.2.2 hnM' hwm.2.1 htM' hwm.1 huM'
    have hmi := methodOk_inv hmo'
    have hlook : forall b, List.Mem b (D.bounds ++ Delta') -> forall U,
        List.Mem (b.X, U) ((dom D.bounds ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs')) ->
        (Ty.var b.X).subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))) = U := by
      intro b _ U hm
      rw [hsg]
      simp only [Ty.subst, lookup_zip_nodup hN hm, Option.getD_some]
    have hbF : forall b, List.Mem b (D.bounds ++ Delta') ->
        Sub d [] ((Ty.var b.X).subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs'))))
          (b.T.subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs')))) /\
        Kind d [] ((Ty.var b.X).subst (GSubst.ty (bind (D.bounds ++ Delta') (Gs ++ Gs')))) := by
      intro b hb
      have hb' := hb
      simp only [listMem_iff, List.mem_append] at hb'
      rcases hb' with hb1 | hb1
      . have hka := (kind_dec_args hwf hD hw.kind).2 b hb1
        have hbT : forall X, List.Mem X (Ty.ftvList [b.T]) -> List.Mem X (dom D.bounds) := by
          intro X hX
          simp only [Ty.ftvList, List.append_nil] at hX
          exact Kind.ftv ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb1)) X hX
        have hbX : forall X, List.Mem X (Ty.ftvList [Ty.var b.X]) -> List.Mem X (dom D.bounds) := by
          intro X hX
          cases hX with
          | head => exact List.mem_map_of_mem (f := Bound.X) hb1
          | tail _ h => cases h
        have e1 := hcomp1 [b.T] hbT
        have e2 := hcomp1 [Ty.var b.X] hbX
        simp only [Ty.substList, List.cons.injEq] at e1 e2
        rw [e1.1, e2.1]
        exact hka
      . have hss := hw.subs
        rw [<- hcod] at hss
        rcases bounds_sat_aux (by rw [gtys_length]; exact hG') hss hw.kinds b hb1 with ⟨U, hU⟩
        have hm : List.Mem (b.X, U) ((dom D.bounds ++ dom Delta').zip (GTy.tys Gs ++ GTy.tys Gs')) := by
          rw [List.zip_append (by simp [gtys_length, hG, dom])]
          simp only [listMem_iff, List.mem_append]
          exact Or.inr hU.1
        rw [hlook b hb U hm]
        exact hU.2
    have hgok : GOk d (D.bounds ++ Delta') (bind (D.bounds ++ Delta') (Gs ++ Gs')) := by
      intro b hb G hl
      have e := var_gsubst_some hl
      have hk := hbF b hb
      rw [e] at hk
      refine And.intro hk.1 (And.intro hk.2 ?_)
      have hKb : Kind d (D.bounds ++ Delta') b.T := by
        simp only [listMem_iff, List.mem_append] at hb
        rcases hb with hb | hb
        . exact Kind.mono (fun x hx => by simp only [listMem_iff, List.mem_append]; exact Or.inl hx)
            ((hok D hD.dec_mem).1 b.T (List.mem_map_of_mem (f := Bound.T) hb))
        . exact hmi.1 b.T (List.mem_map_of_mem (f := Bound.T) hb)
      exact Kind.subst hd (fun b hb => (hbF b hb).1) (fun b hb => (hbF b hb).2) hKb
    have hfst : (bind (D.bounds ++ Delta') (Gs ++ Gs')).map Prod.fst = dom (D.bounds ++ Delta') :=
      bind_fst (by simp [hG, hG'])
    have hs2 := hsig
    simp only [Ty.substList, List.cons.injEq] at hs2
    have hres := found_tail hwf hok hd hmi.2.2 hgok hfst hN' hp (by rw [dom_append]; exact hgs) hvs hnx ht0 hu0 ha'
      (by simp only [Ty.substList, Ty.subst]; rw [hv1.1, hs2.2]; exact hw.args) ha.2.2.2.2.1 (WFExpr.noThis ha)
      (WFExpr.uniq ha)
    rw [hs2.1] at hres
    exact hw.up.typing hres

theorem pres_innerFound {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) {C C' : ClassName}
    {Ms : List Method} {M : Method} {m : MethName} {Delta' : Bounds} {T0 : Ty} {ps : List VarDecl} {e0 : Expr}
    {v0 : Value} {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} {T : Ty} (hv : v0 = Value.newLocal C Gs C' Gs'' vs0 Ms)
    (hM : List.Mem M Ms) (hF : FreshM M (.mk Delta' T0 m ps e0)) (hG' : Gs'.length = Delta'.length)
    (hp : ps.length = vs.length) (hN : (dom Delta').Nodup) (hN' : (this :: ps.map VarDecl.x).Nodup)
    (hgs : GSubstDefined (dom Delta') e0) (hvs : VSubstDefined (this :: ps.map VarDecl.x) e0)
    (ha : WFExpr (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)))
    (ha' : WFExpr ((e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))))
    (h : Typing d [] [] (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] ((e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs))) T := by
  rcases found_body (Xs := []) (T0 := T0) (m := m) ha' hvs hgs hN hN' with ⟨hnx, ht0, hu0, hnM', htM', huM'⟩
  have han := ha.2.2.2.2.1
  simp only [Expr.noShadow, Bool.and_eq_true] at han
  have hat := WFExpr.noThis ha
  simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at hat
  have hau := WFExpr.uniq ha
  have hv0n := han.1
  have hv0t := hat.1
  have hv0u := hau.1
  rw [hv] at hv0n hv0t hv0u
  simp only [Value.expr, Expr.noShadow, Bool.and_eq_true, Expr.vbinders, List.mem_append, not_or,
    Expr.uniq] at hv0n hv0t hv0u
  have hnM : M.noShadow [] [] = true := by
    have := noShadowListM_mem hM hv0n.2
    simpa using this
  have htM : NoThisM M := fun h => hv0t.2 (vbindersListM_mem hM h)
  have huM : M.uniq := uniqList_mem hM hv0u.2
  rcases inv_call h rfl with ⟨⟨C0, Ts0, Delta0, Ts2, Delta1, T0c, psc, body, T0', Ts'⟩, hw⟩
  have vt := value_typing hwf hw.ty0
  have hsv : Sub d [] (typeOf v0) (.cls C0 Ts0) := by
    rcases vt.1 with e | e
    . rw [e]; exact Sub.subRefl
    . exact e.1
  have hk0 : Kind d [] (.cls C0 Ts0) := kind_chain hwf hok hd (by rw [hv] at vt; exact vt.2.2) (by rw [hv] at hsv; exact hsv)
  have hty0 := vt.2.1
  rw [hv] at hsv hty0
  rcases inv_local hty0 rfl with ⟨w2, hw2⟩
  have hD2 := pairing_ground_nil hw2.pair
  have hmeth := hw2.meths M hM
  rw [hD2, abs_ground] at hmeth
  have hover := hw2.over
  rw [hD2] at hover
  rcases consistent_unfold hw2.cons with ⟨Fs', Ts'd, es', Ms'd, hcd, _, hcts, _, hcov⟩
  have hO : OverrideOkM d (.cls C0 Ts0) M := by
    rcases Sub.loc_step hwf hcd hsv with e | e
    . simp only [Ty.cls.injEq] at e
      rcases e with ⟨e1, e2⟩
      subst e1 e2
      have := hcov M hM
      rwa [abs_ground] at this
    . have hs2 := e.2
      simp only [Ty.subst] at hs2
      rw [abs_ground] at hcts
      rw [<- hcts] at hs2
      exact hover M C0 Ts0 hM hs2
  have hTs0 : forall X, List.Mem X (Ty.ftvList Ts0) -> False := fun X hX => by
    have := Kind.ftv hk0 X (by simpa [Ty.ftv] using hX)
    cases this
  have hO' := OverrideOkM.ren (rv := []) (rt := []) hwf hok hO hF.1 (fun X hX _ => hTs0 X hX) huM
  rw [Ty.renList_id (fun _ _ => rn_nil)] at hO'
  rcases found_sig hwf hw.scope hw.meth hw.len2 hO' with ⟨eT2, h4, h5, h6⟩
  have hsg : GSubst.ty (bind Delta' Gs') = (dom Delta').zip (GTy.tys Gs') := by rw [gsubst_ty_bind]; rfl
  have hv1 : Ty.substList (GSubst.ty (bind Delta' Gs')) (vars (dom Delta')) = GTy.tys Gs' := by
    rw [hsg]; exact vars_subst hN (by simp [gtys_length, hG', dom])
  have hT2 : Ty.substList (GSubst.ty (bind Delta' Gs')) Ts2 = Ts2 := by
    apply Ty.substList_id
    intro X hX
    have e : Ts2 = Ts0 := eT2
    rw [e] at hX
    exact absurd hX (fun h => hTs0 X h)
  have hcl0 := methodIn_closed hwf hok hw.scope hw.meth
  have hlen0 : (Ts2 ++ vars (dom Delta')).length = (Delta0 ++ Delta1).length := by simp [hw.len2, h4, vars, dom]
  have hcomp2 : forall L, (forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom (Delta0 ++ Delta1))) ->
      Ty.substList (GSubst.ty (bind Delta' Gs'))
        (Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ vars (dom Delta'))) L) =
        Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ GTy.tys Gs')) L := by
    intro L hL
    rw [substList_bind_comp hlen0 hL, substList_app, hT2, hv1]
  have hsig : Ty.substList (GSubst.ty (bind Delta' Gs')) (T0 :: ps.map VarDecl.T) = T0' :: Ts' := by
    rw [<- h6, hcomp2 _ hcl0.1]; exact hw.sig.symm
  have hcod : Ty.substList (GSubst.ty (bind Delta' Gs')) (cod Delta') =
      Ty.substList (bind (Delta0 ++ Delta1) (Ts2 ++ GTy.tys Gs')) (cod Delta1) := by
    rw [<- h5, hcomp2 _ hcl0.2]
  have env : REnv [] [] [] [] [{ T := .cls C (GTy.tys Gs), x := this }]
      [{ T := .cls C (GTy.tys Gs), x := this }] [] [this] [this] :=
    { bD := fun _ h => by cases h
      dX := fun _ h => by cases h
      dT := fun _ h => by cases h
      g := fun z U hl => by rw [rn_nil, Ty.ren_id (fun _ _ => rn_nil)]; exact hl
      gT := fun y hy X hX => by
        cases hy with
        | head => simp [Ty.ftv, GTy.ftv_tys] at hX
        | tail _ h => cases h
      gN := by simp [gdom]
      gx := fun y hy => hy
      gx' := fun y hy => hy
      kv := fun _ h => by cases h }
  have hmeth' : MethodOk d [] [{ T := .cls C (GTy.tys Gs), x := this }] M := by
    simpa [withoutThis, restrict] using hmeth
  have hmo' := MethodOk.ren hwf hok hd hmeth' hF.1 env hnM hnM' htM htM' huM huM'
  have hmi := methodOk_inv hmo'
  simp only [List.nil_append] at hmi
  have hbF : forall b, List.Mem b Delta' ->
      Sub d [] ((Ty.var b.X).subst (GSubst.ty (bind Delta' Gs'))) (b.T.subst (GSubst.ty (bind Delta' Gs'))) /\
      Kind d [] ((Ty.var b.X).subst (GSubst.ty (bind Delta' Gs'))) := by
    intro b hb
    have hss := hw.subs
    rw [<- hcod] at hss
    rcases bounds_sat_aux (by rw [gtys_length]; exact hG') hss hw.kinds b hb with ⟨U, hU⟩
    rw [hsg]
    simp only [Ty.subst, lookup_zip_nodup hN hU.1, Option.getD_some]
    rw [<- hsg]
    exact hU.2
  have hgok : GOk d Delta' (bind Delta' Gs') := by
    intro b hb G hl
    have e := var_gsubst_some hl
    have hk := hbF b hb
    rw [e] at hk
    exact And.intro hk.1 (And.intro hk.2 (Kind.subst hd (fun b hb => (hbF b hb).1) (fun b hb => (hbF b hb).2)
      (hmi.1 b.T (List.mem_map_of_mem (f := Bound.T) hb))))
  have hfst : (bind Delta' Gs').map Prod.fst = dom Delta' := bind_fst hG'
  have htv0 : Typing d [] [] v0.expr (.cls C (GTy.tys Gs)) := by
    have := vt.2.1
    rw [hv] at this |-
    simpa [typeOf] using this
  have hs2 := hsig
  simp only [Ty.substList, List.cons.injEq] at hs2
  have eg : (Ty.cls C (GTy.tys Gs)).subst (GSubst.ty (bind Delta' Gs')) = Ty.cls C (GTy.tys Gs) :=
    GTy.subst_ty (GTy.cls C Gs)
  have hres := found_tail hwf hok hd hmi.2.2 hgok hfst hN' hp hgs hvs hnx ht0 hu0 ha'
    (by simp only [Ty.substList]; rw [eg, hs2.2]; exact TypingSeq.cons htv0 hw.args) ha.2.2.2.2.1 (WFExpr.noThis ha)
    (WFExpr.uniq ha)
  rw [hs2.1] at hres
  exact hw.up.typing hres

theorem preservationBase {d : Decls} {a a' : Expr} {T : Ty} (hwf : WFDecls d) (hok : DeclsOk d) (ha : WFExpr a)
    (ha' : WFExpr a') (hs : BaseStep d a a') (ht : Typing d [] [] a T) : Typing d [] [] a' T := by
  have hd := declOk hwf hok
  cases hs with
  | simpleFieldFound h1 h2 h3 => exact pres_fieldFound hwf h1 h2 h3 ht
  | simpleFieldSuper h1 h2 h3 h4 h5 => exact pres_simpleFieldSuper hwf h1 h2 h3 h4 ht
  | innerFieldSuper => exact pres_innerFieldSuper hwf ht
  | ifThen h1 h2 h3 => exact pres_ifThen hwf hok hd h1 h2 h3 ha ha' ht
  | ifElse h1 => exact pres_ifElse ht
  | simpleAddSuper h1 => exact pres_addSuper hwf h1 ht
  | simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    subst h11
    exact pres_simpleFound hwf hok hd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ha ha' ht
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    subst h10
    exact pres_innerFound hwf hok hd h1 h2 h3 h4 h5 h6 h7 h8 h9 ha ha' ht
  | innerSuper h1 h2 => exact pres_innerSuper hwf h1 h2 ht
  | searchSuper h1 h2 h3 h4 => exact pres_searchSuper hwf hok hd h1 h2 h4 ht

end Funnelling
