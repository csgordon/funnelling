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
  cases inv_if h rfl with
  | intro w hw => exact hw.up.typing hw.ty2

theorem pres_addSuper {d : Decls} (hwf : WFDecls d) {C : ClassName} {m : MethName} {v : Value}
    {Gs Gs' : List GTy} {vs0 vs : List Value} {T : Ty} (hv : v = Value.new C Gs vs0)
    (h : Typing d [] [] (.call v.expr (GTy.tys Gs') m (Value.exprs vs)) T) :
    Typing d [] [] (.superCall v.expr (.cls C (GTy.tys Gs)) (GTy.tys Gs') m (Value.exprs vs)) T := by
  cases inv_call h rfl with
  | intro w hw =>
    have vt := value_typing hwf hw.ty0
    subst hv
    cases value_new_declared hwf vt.2.1 with
    | intro D hD =>
      have hn := hD.2
      subst hn
      have hsub := vt.1.sub
      simp only [typeOf] at hsub
      cases Sub.top_target hwf hD.1 hsub with
      | intro D0 hD0 =>
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
  cases inv_super h rfl with
  | intro w hw =>
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

end Funnelling.High