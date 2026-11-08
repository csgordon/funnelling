import Funnelling.Sound.Determinism

open Funnelling.SoundSimp

namespace Funnelling

theorem Sub.trans {d : Decls} {Delta : Bounds} {T1 T2 T3 : Ty} (h1 : Sub d Delta T1 T2)
    (h2 : Sub d Delta T2 T3) : Sub d Delta T1 T3 := by
  induction h1 with
  | subRefl => exact h2
  | subInherit hD hl _ ih => exact .subInherit hD hl (ih h2)
  | subInheritLocal hD hl _ ih => exact .subInheritLocal hD hl (ih h2)
  | subVar hm _ ih => exact .subVar hm (ih h2)

abbrev Up (d : Decls) (Delta : Bounds) (T1 T : Ty) : Prop :=
  T1 = T \/ (Sub d Delta T1 T /\ Kind d Delta T)

theorem Up.refl {d : Decls} {Delta : Bounds} {T : Ty} : Up d Delta T T := Or.inl rfl

theorem Up.trans {d : Decls} {Delta : Bounds} {T1 T2 T3 : Ty} (h1 : Up d Delta T1 T2) (h2 : Up d Delta T2 T3) :
    Up d Delta T1 T3 := by
  rcases h1 with e | h1
  . subst e; exact h2
  . rcases h2 with e | h2
    . subst e; exact Or.inr h1
    . exact Or.inr (And.intro (h1.1.trans h2.1) h2.2)

theorem Up.typing {d : Decls} {Delta : Bounds} {gamma : Gamma} {e : Expr} {T1 T : Ty}
    (h : Typing d Delta gamma e T1) (hu : Up d Delta T1 T) : Typing d Delta gamma e T := by
  rcases hu with e | hu
  . subst e; exact h
  . exact Typing.subs h hu.2 hu.1

theorem Up.sub {d : Decls} {Delta : Bounds} {T1 T : Ty} (h : Up d Delta T1 T) : Sub d Delta T1 T := by
  rcases h with e | h
  . subst e; exact Sub.subRefl
  . exact h.1

structure FieldW where
  D : Dec
  Ts' : List Ty
  T0 : Ty

structure FieldP (d : Decls) (Delta : Bounds) (gamma : Gamma) (e : Expr) (f : FieldName) (T : Ty) (w : FieldW) : Prop where
  ty : Typing d Delta gamma e (.cls w.D.C w.Ts')
  decl : Declared d (.dec w.D)
  mem : List.Mem { T := w.T0, f := f } w.D.Ss
  len : w.Ts'.length = w.D.bounds.length
  up : Up d Delta (w.T0.subst (bind w.D.bounds w.Ts')) T

theorem inv_field {d Delta gamma e0 f} : forall {e T}, Typing d Delta gamma e T -> e = .field e0 f ->
    exists w, FieldP d Delta gamma e0 f T w
  | _, _, .subs h hk hs, he => by
    rcases inv_field h he with ⟨w, hw⟩; exact Exists.intro w { hw with up := hw.up.trans (Or.inr (And.intro hs hk)) }
  | _, _, .declField h1 h2 h3 h4, he => by
    cases he
    exact Exists.intro { D := _, Ts' := _, T0 := _ } { ty := h1, decl := h2, mem := h3, len := h4, up := Up.refl }
  | _, _, .var .., he => by cases he
  | _, _, .newObject, he => by cases he
  | _, _, .call .., he => by cases he
  | _, _, .callLbRuntime .., he => by cases he
  | _, _, .newTop .., he => by cases he
  | _, _, .newLocal .., he => by cases he
  | _, _, .ifInstanceof .., he => by cases he

structure IfW where
  T0 : Ty
  T1 : Ty

structure IfP (d : Decls) (Delta : Bounds) (gamma : Gamma) (e0 : Expr) (T : Ty) (x : VarName) (e1 e2 : Expr)
    (T' : Ty) (w : IfW) : Prop where
  ty0 : Typing d Delta gamma e0 w.T0
  kind : Kind d Delta T
  cast : Cast d Delta w.T0 T
  ty1 : Typing d Delta (gamma ++ [{ T := T, x := x }]) e1 w.T1
  ty2 : Typing d Delta gamma e2 w.T1
  up : Up d Delta w.T1 T'

theorem inv_if {d Delta gamma e0 T x e1 e2} : forall {e T'}, Typing d Delta gamma e T' ->
    e = .ifInst e0 T x e1 e2 -> exists w, IfP d Delta gamma e0 T x e1 e2 T' w
  | _, _, .subs h hk hs, he => by
    rcases inv_if h he with ⟨w, hw⟩; exact Exists.intro w { hw with up := hw.up.trans (Or.inr (And.intro hs hk)) }
  | _, _, .ifInstanceof h0 hk hc h1 h2, he => by
    cases he
    exact Exists.intro { T0 := _, T1 := _ } { ty0 := h0, kind := hk, cast := hc, ty1 := h1, ty2 := h2, up := Up.refl }
  | _, _, .var .., he => by cases he
  | _, _, .newObject, he => by cases he
  | _, _, .declField .., he => by cases he
  | _, _, .call .., he => by cases he
  | _, _, .callLbRuntime .., he => by cases he
  | _, _, .newTop .., he => by cases he
  | _, _, .newLocal .., he => by cases he

structure CallW where
  C0 : ClassName
  Ts0 : List Ty
  Delta0 : Bounds
  Ts2 : List Ty
  Delta1 : Bounds
  T0 : Ty
  ps : List VarDecl
  body : Expr
  T0' : Ty
  Ts' : List Ty

structure CallP (d : Decls) (Delta : Bounds) (gamma : Gamma) (e0 : Expr) (Ts1 : List Ty) (m : MethName)
    (es : List Expr) (T : Ty) (w : CallW) : Prop where
  ty0 : Typing d Delta gamma e0 (.cls w.C0 w.Ts0)
  scope : Scope d (.cls w.C0 w.Ts0) w.Delta0 w.Ts2
  meth : MethodIn d (.mk w.Delta1 w.T0 m w.ps w.body) w.C0
  len2 : w.Ts2.length = w.Delta0.length
  len1 : Ts1.length = w.Delta1.length
  sig : w.T0' :: w.Ts' = Ty.substList (bind (w.Delta0 ++ w.Delta1) (w.Ts2 ++ Ts1)) (w.T0 :: w.ps.map VarDecl.T)
  kinds : KindSeq d Delta Ts1
  subs : SubSeq d Delta Ts1 (Ty.substList (bind (w.Delta0 ++ w.Delta1) (w.Ts2 ++ Ts1)) (cod w.Delta1))
  args : TypingSeq d Delta gamma es w.Ts'
  up : Up d Delta w.T0' T

theorem inv_call {d Delta gamma e0 Ts1 m es} : forall {e T}, Typing d Delta gamma e T ->
    e = .call e0 Ts1 m es -> exists w, CallP d Delta gamma e0 Ts1 m es T w
  | _, _, .subs h hk hs, he => by
    rcases inv_call h he with ⟨w, hw⟩; exact Exists.intro w { hw with up := hw.up.trans (Or.inr (And.intro hs hk)) }
  | _, _, .call h1 h2 h3 h4 h5 h6 h7 h8 h9, he => by
    cases he
    exact Exists.intro (CallW.mk _ _ _ _ _ _ _ _ _ _) (CallP.mk h1 h2 h3 h4 h5 h6 h7 h8 h9 Up.refl)
  | _, _, .var .., he => by cases he
  | _, _, .newObject, he => by cases he
  | _, _, .declField .., he => by cases he
  | _, _, .callLbRuntime .., he => by cases he
  | _, _, .newTop .., he => by cases he
  | _, _, .newLocal .., he => by cases he
  | _, _, .ifInstanceof .., he => by cases he

structure SuperW where
  D : Dec
  Ts : List Ty
  D0 : Dec
  Ts0 : List Ty
  Delta1 : Bounds
  T0 : Ty
  ps : List VarDecl
  body : Expr
  T0' : Ty
  Ts' : List Ty

structure SuperP (d : Decls) (Delta : Bounds) (gamma : Gamma) (e0 : Expr) (T : Ty) (Ts1 : List Ty) (m : MethName)
    (es : List Expr) (T' : Ty) (w : SuperW) : Prop where
  ann : T = .cls w.D.C w.Ts
  sub : Sub d Delta (.cls w.D.C w.Ts) (.cls w.D0.C w.Ts0)
  decl0 : Declared d (.dec w.D0)
  meth : MethodIn d (.mk w.Delta1 w.T0 m w.ps w.body) w.D0.C
  len0 : w.Ts0.length = w.D0.bounds.length
  len1 : Ts1.length = w.Delta1.length
  sig : w.T0' :: w.Ts' = Ty.substList (bind (w.D0.bounds ++ w.Delta1) (w.Ts0 ++ Ts1)) (w.T0 :: w.ps.map VarDecl.T)
  decl : Declared d (.dec w.D)
  kind : Kind d Delta (.cls w.D.C w.Ts)
  kinds : KindSeq d Delta Ts1
  subs : SubSeq d Delta Ts1 (Ty.substList (bind (w.D0.bounds ++ w.Delta1) (w.Ts0 ++ Ts1)) (cod w.Delta1))
  args : TypingSeq d Delta gamma (e0 :: es) (.cls w.D.C w.Ts :: w.Ts')
  up : Up d Delta w.T0' T'

theorem inv_super {d Delta gamma e0 T0 Ts1 m es} : forall {e T}, Typing d Delta gamma e T ->
    e = .superCall e0 T0 Ts1 m es -> exists w, SuperP d Delta gamma e0 T0 Ts1 m es T w
  | _, _, .subs h hk hs, he => by
    rcases inv_super h he with ⟨w, hw⟩; exact Exists.intro w { hw with up := hw.up.trans (Or.inr (And.intro hs hk)) }
  | _, _, .callLbRuntime h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, he => by
    cases he
    exact Exists.intro (SuperW.mk _ _ _ _ _ _ _ _ _ _) (SuperP.mk rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 Up.refl)
  | _, _, .var .., he => by cases he
  | _, _, .newObject, he => by cases he
  | _, _, .declField .., he => by cases he
  | _, _, .call .., he => by cases he
  | _, _, .newTop .., he => by cases he
  | _, _, .newLocal .., he => by cases he
  | _, _, .ifInstanceof .., he => by cases he

structure LocalW where
  Delta' : Bounds
  Ts'' : List Ty
  T'' : Ty

structure LocalP (d : Decls) (Delta : Bounds) (gamma : Gamma) (C : ClassName) (Fs : List Funnel) (C0 : ClassName)
    (Ts : List Ty) (es : List Expr) (Ms : List Method) (T' : Ty) (w : LocalW) : Prop where
  cons : Consistent d (.loc C Fs C0 Ts es Ms)
  pair : Pairing Delta Fs (abs Fs) w.Delta' w.Ts''
  closedB : forall X, List.Mem X (Ty.ftvList (cod w.Delta')) -> List.Mem X (dom w.Delta')
  kindC : Kind d w.Delta' (.cls C (abs Fs))
  kindS : Kind d w.Delta' (.cls C0 Ts)
  tyNew : Typing d Delta gamma (.new C0 Ts es) w.T''
  meths : forall M, List.Mem M Ms -> MethodOk d w.Delta'
    (withoutThis (restrict gamma (Ty.ftvList (abs Fs))) ++ [{ T := .cls C (abs Fs), x := this }]) M
  over : OverrideOk d w.Delta' (.cls C0 Ts) Ms
  up : Up d Delta (.cls C (abs Fs)) T'

theorem inv_local {d Delta gamma C Fs C0 Ts es Ms} : forall {e T}, Typing d Delta gamma e T ->
    e = .newLocal C Fs C0 Ts es Ms -> exists w, LocalP d Delta gamma C Fs C0 Ts es Ms T w
  | _, _, .subs h hk hs, he => by
    rcases inv_local h he with ⟨w, hw⟩; exact Exists.intro w { hw with up := hw.up.trans (Or.inr (And.intro hs hk)) }
  | _, _, .newLocal h1 h2 h3 h4 h5 h6 h7 h8, he => by
    cases he
    exact Exists.intro (LocalW.mk _ _ _) (LocalP.mk h1 h2 h3 h4 h5 h6 h7 h8 Up.refl)
  | _, _, .var .., he => by cases he
  | _, _, .newObject, he => by cases he
  | _, _, .declField .., he => by cases he
  | _, _, .call .., he => by cases he
  | _, _, .callLbRuntime .., he => by cases he
  | _, _, .newTop .., he => by cases he
  | _, _, .ifInstanceof .., he => by cases he

structure NewW where
  D : Dec
  es1 : List Expr
  es2 : List Expr
  T'' : Ty

structure NewP (d : Decls) (Delta : Bounds) (gamma : Gamma) (C : ClassName) (Ts : List Ty) (es : List Expr)
    (T : Ty) (w : NewW) : Prop where
  name : w.D.C = C
  decl : Declared d (.dec w.D)
  kind : Kind d Delta (.cls w.D.C Ts)
  len : Ts.length = w.D.bounds.length
  fields : TypingSeq d Delta gamma w.es1 (Ty.substList (bind w.D.bounds Ts) (w.D.Ss.map Slot.T))
  sup : Typing d Delta gamma (.new w.D.C' (Ty.substList (bind w.D.bounds Ts) w.D.Ts) w.es2) w.T''
  split : es = w.es1 ++ w.es2
  up : Up d Delta (.cls w.D.C Ts) T

theorem inv_new {d Delta gamma C Ts es} : forall {e T}, Typing d Delta gamma e T -> e = .new C Ts es ->
    (C = Object /\ Ts = [] /\ es = [] /\ Up d Delta (.cls Object []) T) \/ exists w, NewP d Delta gamma C Ts es T w
  | _, _, .subs h hk hs, he => by
    rcases inv_new h he with h1 | h1
    . exact Or.inl (And.intro h1.1 (And.intro h1.2.1 (And.intro h1.2.2.1 (h1.2.2.2.trans (Or.inr (And.intro hs hk))))))
    . cases h1 with
      | intro w hw => exact Or.inr (Exists.intro w { hw with up := hw.up.trans (Or.inr (And.intro hs hk)) })
  | _, _, .newObject, he => by
    cases he
    exact Or.inl (And.intro rfl (And.intro rfl (And.intro rfl Up.refl)))
  | _, _, .newTop h1 h2 h3 h4 h5, he => by
    cases he
    exact Or.inr (Exists.intro (NewW.mk _ _ _ _) (NewP.mk rfl h1 h2 h3 h4 h5 rfl Up.refl))
  | _, _, .var .., he => by cases he
  | _, _, .declField .., he => by cases he
  | _, _, .call .., he => by cases he
  | _, _, .callLbRuntime .., he => by cases he
  | _, _, .newLocal .., he => by cases he
  | _, _, .ifInstanceof .., he => by cases he

theorem TypingSeq.mid {d Delta gamma} {x : Expr} : forall {l r : List Expr} {Ts : List Ty},
    TypingSeq d Delta gamma (l ++ x :: r) Ts -> exists Tx, Typing d Delta gamma x Tx /\
      forall x', Typing d Delta gamma x' Tx -> TypingSeq d Delta gamma (l ++ x' :: r) Ts
  | [], r, Ts, h => by
    cases h with
    | cons h1 h2 => exact Exists.intro _ (And.intro h1 (fun x' hx => TypingSeq.cons hx h2))
  | y :: l, r, Ts, h => by
    cases h with
    | cons h1 h2 =>
      cases TypingSeq.mid h2 with
      | intro Tx hx => exact Exists.intro Tx (And.intro hx.1 (fun x' h' => TypingSeq.cons h1 (hx.2 x' h')))

theorem append_cons_split {A : Type} {l r P Q : List A} {x : A} (h : l ++ x :: r = P ++ Q) :
    (exists r1, P = l ++ x :: r1 /\ r = r1 ++ Q) \/ (exists l2, Q = l2 ++ x :: r /\ l = P ++ l2) := by
  rcases List.append_eq_append_iff.mp h with h1 | h1
  . rcases h1 with ⟨a, h1⟩
    cases a with
    | nil =>
      simp_all
    | cons y a =>
      simp_all
  . cases h1 with
    | intro c h1 => exact Or.inr (Exists.intro c (And.intro h1.2 h1.1))

theorem typing_new_mid {d Delta gamma} {x : Expr} : forall {C Ts l r T} {e : Expr},
    Typing d Delta gamma e T -> e = .new C Ts (l ++ x :: r) -> exists Tx, Typing d Delta gamma x Tx /\
      forall x', Typing d Delta gamma x' Tx -> Typing d Delta gamma (.new C Ts (l ++ x' :: r)) T
  | _, _, _, _, _, _, .subs h hk hs, he => by
    cases typing_new_mid h he with
    | intro Tx hx => exact Exists.intro Tx (And.intro hx.1 (fun x' h' => Typing.subs (hx.2 x' h') hk hs))
  | _, _, _, _, _, _, .newObject, he => by
    simp only [Expr.new.injEq] at he
    have := he.2.2
    simp at this
  | C, Ts, l, r, _, _, @Typing.newTop _ _ _ D Ts' es1 es2 T'' h1 h2 h3 h4 h5, he => by
    simp only [Expr.new.injEq] at he
    have hs := he.2.2
    have hC := he.1
    have hT := he.2.1
    subst hC hT
    rcases append_cons_split hs.symm with h | h
    . rcases h with ⟨r1, h⟩
      rw [h.1] at h4
      rcases TypingSeq.mid h4 with ⟨Tx, hx⟩
      refine Exists.intro Tx (And.intro hx.1 (fun x' h' => ?_))
      rw [h.2]
      have e : l ++ x' :: (r1 ++ es2) = (l ++ x' :: r1) ++ es2 := by simp
      rw [e]
      exact Typing.newTop h1 h2 h3 (hx.2 x' h') h5
    . rcases h with ⟨l2, h⟩
      rcases typing_new_mid h5 (by rw [h.1]) with ⟨Tx, hx⟩
      refine Exists.intro Tx (And.intro hx.1 (fun x' h' => ?_))
      rw [h.2, List.append_assoc]
      exact Typing.newTop h1 h2 h3 h4 (hx.2 x' h')
  | _, _, _, _, _, _, .var .., he => by cases he
  | _, _, _, _, _, _, .declField .., he => by cases he
  | _, _, _, _, _, _, .call .., he => by cases he
  | _, _, _, _, _, _, .callLbRuntime .., he => by cases he
  | _, _, _, _, _, _, .newLocal .., he => by cases he
  | _, _, _, _, _, _, .ifInstanceof .., he => by cases he

theorem typing_plug {d Delta gamma} {a : Expr} : forall (E : ECtx) {T : Ty},
    Typing d Delta gamma (E.plug a) T -> exists Ta, Typing d Delta gamma a Ta /\
      forall a', Typing d Delta gamma a' Ta -> Typing d Delta gamma (E.plug a') T
  | .hole, T, h => Exists.intro T (And.intro h (fun _ h' => h'))
  | .callRecv E Gs m es, T, h => by
    rcases inv_call h rfl with ⟨w, hw⟩
    rcases typing_plug E hw.ty0 with ⟨Ta, hTa⟩
    exact Exists.intro Ta (And.intro hTa.1 (fun a' h' => hw.up.typing
      (Typing.call (hTa.2 a' h') hw.scope hw.meth hw.len2 hw.len1 hw.sig hw.kinds hw.subs hw.args)))
  | .callArg v Gs m vs E es, T, h => by
    rcases inv_call h rfl with ⟨w, hw⟩
    rcases TypingSeq.mid hw.args with ⟨Tx, hx⟩
    rcases typing_plug E hx.1 with ⟨Ta, hTa⟩
    exact Exists.intro Ta (And.intro hTa.1 (fun a' h' => hw.up.typing
      (Typing.call hw.ty0 hw.scope hw.meth hw.len2 hw.len1 hw.sig hw.kinds hw.subs (hx.2 _ (hTa.2 a' h')))))
  | .superRecv E G Gs m es, T, h => by
    rcases inv_super h rfl with ⟨w, hw⟩
    have hann := hw.ann
    cases hw.args with
    | cons h0 hs =>
      rcases typing_plug E h0 with ⟨Ta, hTa⟩
      refine Exists.intro Ta (And.intro hTa.1 (fun a' h' => ?_))
      simp only [ECtx.plug]
      rw [hann]
      exact hw.up.typing (Typing.callLbRuntime hw.sub hw.decl0 hw.meth hw.len0 hw.len1 hw.sig hw.decl hw.kind
        hw.kinds hw.subs (TypingSeq.cons (hTa.2 a' h') hs))
  | .superArg v G Gs m vs E es, T, h => by
    rcases inv_super h rfl with ⟨w, hw⟩
    have hann := hw.ann
    cases hw.args with
    | cons h0 hs =>
      rcases TypingSeq.mid hs with ⟨Tx, hx⟩
      rcases typing_plug E hx.1 with ⟨Ta, hTa⟩
      refine Exists.intro Ta (And.intro hTa.1 (fun a' h' => ?_))
      simp only [ECtx.plug]
      rw [hann]
      exact hw.up.typing (Typing.callLbRuntime hw.sub hw.decl0 hw.meth hw.len0 hw.len1 hw.sig hw.decl hw.kind
        hw.kinds hw.subs (TypingSeq.cons h0 (hx.2 _ (hTa.2 a' h'))))
  | .field E f, T, h => by
    rcases inv_field h rfl with ⟨w, hw⟩
    rcases typing_plug E hw.ty with ⟨Ta, hTa⟩
    exact Exists.intro Ta (And.intro hTa.1 (fun a' h' => hw.up.typing
      (Typing.declField (hTa.2 a' h') hw.decl hw.mem hw.len)))
  | .newArg C Gs vs E es, T, h => by
    rcases typing_new_mid h rfl with ⟨Tx, hx⟩
    cases typing_plug E hx.1 with
    | intro Ta hTa => exact Exists.intro Ta (And.intro hTa.1 (fun a' h' => hx.2 _ (hTa.2 a' h')))
  | .localArg C Gs C' Gs' vs E es Ms, T, h => by
    rcases inv_local h rfl with ⟨w, hw⟩
    rcases typing_new_mid hw.tyNew rfl with ⟨Tx, hx⟩
    rcases typing_plug E hx.1 with ⟨Ta, hTa⟩
    exact Exists.intro Ta (And.intro hTa.1 (fun a' h' => hw.up.typing
      (Typing.newLocal hw.cons hw.pair hw.closedB hw.kindC hw.kindS (hx.2 _ (hTa.2 a' h')) hw.meths hw.over)))
  | .ifCond E G x e1 e2, T, h => by
    rcases inv_if h rfl with ⟨w, hw⟩
    rcases typing_plug E hw.ty0 with ⟨Ta, hTa⟩
    exact Exists.intro Ta (And.intro hTa.1 (fun a' h' => hw.up.typing
      (Typing.ifInstanceof (hTa.2 a' h') hw.kind hw.cast hw.ty1 hw.ty2)))

end Funnelling
