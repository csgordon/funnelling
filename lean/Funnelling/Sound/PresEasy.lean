import Funnelling.Sound.Values

open Funnelling.SoundSimp

namespace Funnelling.High

theorem value_new_declared {d : Decls} (hwf : WFDecls d) {C : ClassName} {Gs : List GTy} {vs : List Value} {T : Ty}
    (h : Typing d [] [] (Value.new C Gs vs).expr T) : exists D, Declared d (.dec D) /\ D.C = C := by
  simp only [Value.expr] at h
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
  simp only [typeOf] at hsub
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
  simp only [typeOf] at vt2 vk
  exact hw.up.typing (Typing.callLbRuntime hsub hD0.1 hmeth hlen2 hw.len1 hsig hD.1 vk hw.kinds hsubs
    (TypingSeq.cons vt2 hw.args))

theorem gtys_length {Gs : List GTy} : (GTy.tys Gs).length = Gs.length := by
  rw [GTy.tys_eq_map]; simp

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
  . cases Declared.super hwf hD with
    | intro D' hD' =>
      have hsup := hD'.2
      simp only [K.sup] at hsup
      have hcls := (hok D hD.dec_mem).2.1 _ (List.Mem.head _)
      have hka := kind_dec_args hwf hD hkind
      have hK := Kind.subst hd (Delta' := []) (s := bind D.bounds (GTy.tys Gs)) (fun b hb => (hka.2 b hb).1)
        (fun b hb => (hka.2 b hb).2) hcls
      simp only [Ty.subst] at hK hs
      rw [<- hsup] at hK hs |-
      cases hargs with
      | cons hv hrest =>
        have hv' := Typing.subs hv hK (Sub.subInherit hD (by rw [gtys_length, hG])
          (by simp only [Ty.subst]; rw [<- hsup]; exact Sub.subRefl))
        exact hw.up.typing (Typing.callLbRuntime hs.2 hw.decl0 hw.meth hw.len0 hw.len1 hw.sig hD'.1 hK
          hw.kinds hw.subs (TypingSeq.cons hv' hrest))

theorem consistent_unfold {d : Decls} {C : ClassName} {Fs : List Funnel} {C0 : ClassName} {Ts : List Ty}
    {es : List Expr} {Ms : List Method} (h : Consistent d (.loc C Fs C0 Ts es Ms)) :
    exists Fs' Ts' es' Ms', Declared d (.loc C Fs' C0 Ts' es' Ms') /\ Fs.length = Fs'.length /\
      Ts = Ty.substList (bindF Fs' (abs Fs)) Ts' /\
      (forall m, List.Mem m (Ms'.map Method.name) <-> List.Mem m (Ms.map Method.name)) /\
      (forall M, List.Mem M Ms -> OverrideOkM d (.cls C (abs Fs)) M) := h

theorem abs_length {Fs : List Funnel} : (abs Fs).length = Fs.length := by simp [abs]

theorem pres_innerSuper {d : Decls} (hwf : WFDecls d) {C C' : ClassName} {Ms : List Method} {m : MethName}
    {v0 : Value} {Gs0 Gs Gs' : List GTy} {vs0 vs : List Value} {T : Ty}
    (hv : v0 = Value.newLocal C Gs0 C' Gs vs0 Ms) (hm : Not (List.Mem m (Ms.map Method.name)))
    (h : Typing d [] [] (.call v0.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] (.superCall v0.expr (.cls C' (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T := by
  rcases inv_call h rfl with ⟨w, hw⟩
  have vt := value_typing hwf hw.ty0
  subst hv
  have ty0 := hw.ty0
  simp only [Value.expr] at ty0
  rcases inv_local ty0 rfl with ⟨w2, hw2⟩
  cases consistent_unfold hw2.cons with
  | intro Fs' h' => cases h' with
    | intro Ts' h' => cases h' with
      | intro es' h' => cases h' with
        | intro Ms' hc =>
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
            simp only [typeOf] at hv0
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
  . cases h1 with
    | intro w hw =>
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
  simp only [Value.expr] at ty
  rcases inv_local ty rfl with ⟨w2, hw2⟩
  cases consistent_unfold hw2.cons with
  | intro Fs' h' => cases h' with
    | intro Ts' h' => cases h' with
      | intro es' h' => cases h' with
        | intro Ms' hc =>
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
              simp only [Value.expr]
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
      simp only [Value.expr] at ty
      rcases inv_new ty rfl with h1 | h1
      . exact absurd h1.1 hO
      . cases h1 with
        | intro w3 hw3 =>
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
          simp only [Ty.subst] at hs3
          exact hw.up.typing (Typing.declField (Typing.subs hnew hs.2 hs3) hw.decl hw.mem hw.len)

end Funnelling.High