import Funnelling.Sound.FoundMethod

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
    Expr.noShadow_mono ((Expr.vsubst_back _ _).2.2 _ _ ha'.2.2.2.2.1) (fun _ _ hX => hX)
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
    exact pres_simpleFound hwf hok hd h1 h2 h4 ⟨h3, h5, h8, h6, h7, h9, h10, ha'⟩ ha ht
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    subst h10
    exact pres_innerFound hwf hok hd h1 h2 ⟨h3, h4, h5, h6, h7, h8, h9, ha'⟩ ha ht
  | innerSuper h1 h2 => exact pres_innerSuper hwf h1 h2 ht
  | searchSuper h1 h2 h3 h4 => exact pres_searchSuper hwf hok hd h1 h2 h4 ht

end Funnelling
