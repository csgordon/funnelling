import Funnelling.Sound.Inversion

open Funnelling.SoundSimp

namespace Funnelling

abbrev LocClosed (L : List K) : Prop := forall k, List.Mem k L -> Sub1 (Method.localsList k.Ms) L

theorem LocClosed.append {L1 L2 : List K} (h1 : LocClosed L1) (h2 : LocClosed L2) : LocClosed (L1 ++ L2) := by
  intro k hk x hx
  simp only [listMem_iff, List.mem_append] at hk |-
  rcases hk with hk | hk
  . exact Or.inl (h1 k hk x hx)
  . exact Or.inr (h2 k hk x hx)

mutual
theorem Expr.locClosed : forall (e : Expr), LocClosed e.locals
  | .var _ => fun _ h => by cases h
  | .call e _ _ es => by simp only [Expr.locals]; exact (Expr.locClosed e).append (Expr.locClosedList es)
  | .superCall e _ _ _ es => by simp only [Expr.locals]; exact (Expr.locClosed e).append (Expr.locClosedList es)
  | .field e _ => by simp only [Expr.locals]; exact Expr.locClosed e
  | .new _ _ es => by simp only [Expr.locals]; exact Expr.locClosedList es
  | .newLocal C Fs C' Ts es Ms => by
    intro k hk x hx
    cases hk with
    | head => exact List.Mem.tail _ (List.mem_append_right _ hx)
    | tail _ hk =>
      exact List.Mem.tail _ (((Expr.locClosedList es).append (Method.locClosedList Ms)) k hk x hx)
  | .ifInst e0 _ _ e1 e2 => ((Expr.locClosed e0).append (Expr.locClosed e1)).append (Expr.locClosed e2)
theorem Expr.locClosedList : forall (es : List Expr), LocClosed (Expr.localsList es)
  | [] => fun _ h => by cases h
  | e :: es => by simp only [Expr.localsList]; exact (Expr.locClosed e).append (Expr.locClosedList es)
theorem Method.locClosed : forall (M : Method), LocClosed M.locals
  | .mk _ _ _ _ e => by simp only [Method.locals]; exact Expr.locClosed e
theorem Method.locClosedList : forall (Ms : List Method), LocClosed (Method.localsList Ms)
  | [] => fun _ h => by cases h
  | M :: Ms => by simp only [Method.localsList]; exact (Method.locClosed M).append (Method.locClosedList Ms)
end

theorem classes_locClosed (d : Decls) : LocClosed (classes d) := by
  intro k hk x hx
  simp only [classes, listMem_iff, List.mem_flatMap] at hk |-
  rcases hk with ⟨D, hD⟩
  refine Exists.intro D (And.intro hD.1 ?_)
  cases hD.2 with
  | head => exact List.Mem.tail _ hx
  | tail _ hk => exact List.Mem.tail _ (Method.locClosedList D.Ms k hk x hx)

theorem ExprCtx.locals_plug {a : Expr} {k : K} (hk : List.Mem k a.locals) :
    forall (E : ExprCtx), List.Mem k (E.plug a).locals := by
  intro E
  induction E <;> simp only [ExprCtx.plug, Expr.locals]
  case hole => exact hk
  all_goals
    rename_i ih
    first | exact List.mem_append_left _ ih | exact ih | exact Expr.mem_localsList mem_mid ih
          | exact List.mem_append_right _ (Expr.mem_localsList mem_mid ih) | exact List.mem_append_right _ ih
          | exact List.Mem.tail _ (List.mem_append_left _ (Expr.mem_localsList mem_mid ih))
          | exact List.mem_append_left _ (List.mem_append_left _ ih)
          | exact List.mem_append_left _ (List.mem_append_right _ ih)

theorem OccursIn.locals {C Fs C' Ts es Ms} {e : Expr} (h : OccursIn (.newLocal C Fs C' Ts es Ms) e) :
    List.Mem (K.loc C Fs C' Ts es Ms) e.locals := by
  rcases h with ⟨E, hE⟩; rw [hE]; exact ExprCtx.locals_plug (List.Mem.head _) E

theorem Declared.mem {d : Decls} {k : K} (h : Declared d k) : List.Mem k (classes d) := by
  induction h with
  | dec h => exact classes_mem_dec h
  | @loc k Delta T0 m ps e C0 Fs C' Ts es Ms hk hM hO ih =>
    exact classes_locClosed d k ih _ (Method.mem_localsList hM hO.locals)

theorem Declared.unique {d : Decls} (hwf : WFDecls d) {k1 k2 : K} (h1 : Declared d k1) (h2 : Declared d k2)
    (he : k1.name = k2.name) : k1 = k2 :=
  nodup_map_inj hwf.1 h1.mem h2.mem he

theorem Declared.dec_loc {d : Decls} (hwf : WFDecls d) {D : Dec} {C Fs C' Ts es Ms}
    (h1 : Declared d (.dec D)) (h2 : Declared d (.loc C Fs C' Ts es Ms)) (he : D.C = C) : False := by
  have := Declared.unique hwf h1 h2 he
  cases this

theorem MethodIn.dec {d : Decls} (hwf : WFDecls d) {M : Method} {D : Dec} (hD : Declared d (.dec D))
    (h : MethodIn d M D.C) : List.Mem M D.Ms := by
  rcases h with ⟨k, hk⟩
  have := Declared.unique hwf hk.1 hD hk.2.1
  subst this
  exact hk.2.2

theorem MethodIn.loc {d : Decls} (hwf : WFDecls d) {M : Method} {C Fs C' Ts es Ms}
    (hD : Declared d (.loc C Fs C' Ts es Ms)) (h : MethodIn d M C) : List.Mem M Ms := by
  rcases h with ⟨k, hk⟩
  have := Declared.unique hwf hk.1 hD hk.2.1
  subst this
  exact hk.2.2

theorem names_unique {Ms : List Method} {M1 M2 : Method} (hn : (Ms.map Method.name).Nodup) (h1 : List.Mem M1 Ms)
    (h2 : List.Mem M2 Ms) (he : M1.name = M2.name) : M1 = M2 :=
  nodup_map_inj hn h1 h2 he

theorem Declared.namesNodup {d : Decls} (hwf : WFDecls d) {k : K} (h : Declared d k) : (k.Ms.map Method.name).Nodup :=
  hwf.2.2.1 k h.mem

theorem Sub.dec_step {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} (hD : Declared d (.dec D))
    {Ts : List Ty} {T : Ty} (h : Sub d Delta (.cls D.C Ts) T) :
    T = .cls D.C Ts \/ (Ts.length = D.bounds.length /\ Sub d Delta ((Ty.cls D.C' D.Ts).subst (bind D.bounds Ts)) T) := by
  generalize he : Ty.cls D.C Ts = T0 at h
  cases h with
  | subRefl => exact Or.inl rfl
  | @subInherit D' Ts0 T' hD' hl h' =>
    simp only [Ty.cls.injEq] at he
    have e := Declared.unique hwf hD' hD he.1.symm
    cases e
    rw [he.2]
    exact Or.inr (And.intro hl h')
  | subInheritLocal hD' _ _ =>
    simp only [Ty.cls.injEq] at he
    exact absurd (Declared.dec_loc hwf hD hD' he.1) id
  | subVar => cases he

theorem Sub.loc_step {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {C Fs C' Ts' es Ms}
    (hD : Declared d (.loc C Fs C' Ts' es Ms)) {Ts : List Ty} {T : Ty} (h : Sub d Delta (.cls C Ts) T) :
    T = .cls C Ts \/ (Ts.length = Fs.length /\ Sub d Delta ((Ty.cls C' Ts').subst (bindF Fs Ts)) T) := by
  generalize he : Ty.cls C Ts = T0 at h
  cases h with
  | subRefl => exact Or.inl rfl
  | subInherit hD' _ _ =>
    simp only [Ty.cls.injEq] at he
    exact absurd (Declared.dec_loc hwf hD' hD he.1.symm) id
  | @subInheritLocal C2 Fs2 C2' Ts2' es2 Ms2 Ts2 T' hD' hl h' =>
    simp only [Ty.cls.injEq] at he
    have e := Declared.unique hwf hD' hD he.1.symm
    cases e
    rw [he.2]
    exact Or.inr (And.intro hl h')
  | subVar => cases he

theorem Scope.loc_declared {d : Decls} {Delta0 : Bounds} {Ts0 : List Ty} {C0 : ClassName} {Ts : List Ty}
    (h : Scope d (.cls C0 Ts) Delta0 Ts0) :
    (exists D, Declared d (.dec D) /\ D.C = C0 /\ Delta0 = D.bounds /\ Ts0 = Ts) \/
    (exists Fs C' Ts' es Ms Delta, Declared d (.loc C0 Fs C' Ts' es Ms) /\ Pairing Delta Fs Ts Delta0 Ts0) := by
  generalize he : Ty.cls C0 Ts = T at h
  cases h with
  | @dec D Ts2 hD =>
    simp only [Ty.cls.injEq] at he
    exact Or.inl (Exists.intro D (And.intro hD (And.intro he.1.symm (And.intro rfl he.2.symm))))
  | @loc C Delta' T0 m ps e C1 Fs C' Ts' es Ms T Delta Ts'' Ts2 Delta0 Ts0 h1 h2 h3 h4 h5 =>
    simp only [Ty.cls.injEq] at he
    rcases h1 with ⟨k, hk⟩
    have hd := Declared.loc hk.1 (by rw [hk.2.1] at hk; exact hk.2.2) h2
    rw [he.1, he.2] at *
    exact Or.inr (Exists.intro Fs (Exists.intro C' (Exists.intro Ts' (Exists.intro es (Exists.intro Ms
      (Exists.intro _ (And.intro hd h5)))))))

theorem Scope.dec_eq {d : Decls} (hwf : WFDecls d) {D : Dec} (hD : Declared d (.dec D)) {Ts Ts0 : List Ty}
    {Delta0 : Bounds} (h : Scope d (.cls D.C Ts) Delta0 Ts0) : Delta0 = D.bounds /\ Ts0 = Ts := by
  rcases h.loc_declared with h' | h'
  . rcases h' with ⟨D', h'⟩
    have e := Declared.unique hwf h'.1 hD h'.2.1
    cases e
    exact h'.2.2
  . rcases h' with ⟨Fs, C', Ts', es, Ms, Delta, h'⟩
    exact absurd (Declared.dec_loc hwf hD h'.1 rfl) id

theorem find_some {A : Type} {p : A -> Bool} : forall {l : List A} {x : A}, l.find? p = some x ->
    List.Mem x l /\ p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    by_cases ha : p a = true
    . simp_all
    . rw [List.find?_cons_of_neg ha] at h
      have r := find_some h
      exact And.intro (List.Mem.tail _ r.1) r.2

theorem Declared.super {d : Decls} (hwf : WFDecls d) {k : K} (hk : Declared d k) :
    exists D', Declared d (.dec D') /\ D'.C = k.sup := by
  have h := hwf.2.2.2.2.2.2.2.2.2.1 k hk.mem
  cases hf : findDec d k.sup with
  | none => rw [hf] at h; cases h
  | some D' =>
    have r := find_some hf
    exact Exists.intro D' (And.intro (Declared.dec r.1) (by simpa using r.2))

theorem pairing_ground_nil {Delta : Bounds} : forall {Gs : List GTy} {Ts : List Ty} {Delta' : Bounds} {Ts'' : List Ty},
    Pairing Delta (Gs.map Funnel.ground) Ts Delta' Ts'' -> Delta' = []
  | [], _, _, _, h => by cases h; rfl
  | G :: Gs, _, _, _, h => by
    cases h with
    | ground h => exact pairing_ground_nil h

theorem abs_ground {Gs : List GTy} : abs (Gs.map Funnel.ground) = GTy.tys Gs := by
  rw [GTy.tys_eq_map]
  simp [abs, List.map_map, Function.comp_def, Funnel.abs]

theorem consistent_unfold {d : Decls} {C : ClassName} {Fs : List Funnel} {C0 : ClassName} {Ts : List Ty}
    {es : List Expr} {Ms : List Method} (h : Consistent d (.loc C Fs C0 Ts es Ms)) :
    exists Fs' Ts' es' Ms', Declared d (.loc C Fs' C0 Ts' es' Ms') /\ Fs.length = Fs'.length /\
      Ts = Ty.substList (bindF Fs' (abs Fs)) Ts' /\
      (forall m, List.Mem m (Ms'.map Method.name) <-> List.Mem m (Ms.map Method.name)) /\
      (forall M, List.Mem M Ms -> OverrideOkM d (.cls C (abs Fs)) M) := h

theorem abs_length {Fs : List Funnel} : (abs Fs).length = Fs.length := by simp [abs]

theorem occ_typing {d : Decls} {Delta : Bounds} {a : Expr} : forall (E : ExprCtx) {gamma : Gamma} {T : Ty},
    Typing d Delta gamma (E.plug a) T -> exists gamma' Ta, Typing d Delta gamma' a Ta
  | .hole, gamma, T, h => ⟨gamma, T, h⟩
  | .callRecv E _ _ _, _, _, h => let ⟨_, hw⟩ := inv_call h rfl; occ_typing E hw.ty0
  | .callArg _ _ _ _ E _, _, _, h => let ⟨_, hw⟩ := inv_call h rfl; let ⟨_, hx⟩ := TypingSeq.mid hw.args; occ_typing E hx.1
  | .superRecv E _ _ _ _, _, _, h => by
    rcases inv_super h rfl with ⟨_, hw⟩; cases hw.args with | cons h0 _ => exact occ_typing E h0
  | .superArg _ _ _ _ _ E _, _, _, h => by
    rcases inv_super h rfl with ⟨_, hw⟩
    cases hw.args with | cons _ hs => exact let ⟨_, hx⟩ := TypingSeq.mid hs; occ_typing E hx.1
  | .field E _, _, _, h => let ⟨_, hw⟩ := inv_field h rfl; occ_typing E hw.ty
  | .newArg _ _ _ E _, _, _, h => let ⟨_, hx⟩ := typing_new_mid h rfl; occ_typing E hx.1
  | .localArg _ _ _ _ _ E _ _, _, _, h =>
    let ⟨_, hw⟩ := inv_local h rfl; let ⟨_, hx⟩ := typing_new_mid hw.tyNew rfl; occ_typing E hx.1
  | .ifCond E _ _ _ _, _, _, h => let ⟨_, hw⟩ := inv_if h rfl; occ_typing E hw.ty0
  | .ifThen _ _ _ E _, _, _, h => let ⟨_, hw⟩ := inv_if h rfl; occ_typing E hw.ty1
  | .ifElse _ _ _ _ E, _, _, h => let ⟨_, hw⟩ := inv_if h rfl; occ_typing E hw.ty2

theorem occ_noShadow {Xs : List TVarName} {C Fs C' Ts es Ms} : forall (E : ExprCtx) {xs : List VarName},
    (E.plug (.newLocal C Fs C' Ts es Ms)).noShadow Xs xs = true -> exists xs', Method.noShadowList Xs xs' Ms = true := by
  intro E
  induction E <;> intro xs h <;> simp only [ExprCtx.plug, Expr.noShadow, Bool.and_eq_true] at h
  case hole => exact Exists.intro _ h.2
  all_goals
    rename_i ih
    first | exact ih h | exact ih h.1 | exact ih h.2 | exact ih h.1.1.1 | exact ih h.1.2
          | exact ih (Expr.noShadowList_mem mem_mid h) | exact ih (Expr.noShadowList_mem mem_mid h.1)
          | exact ih (Expr.noShadowList_mem mem_mid h.2)

theorem Pairing.dom_eq {Delta : Bounds} {Fs : List Funnel} {Ts : List Ty} {Delta0 : Bounds} {Ts0 : List Ty}
    (h : Pairing Delta Fs Ts Delta0 Ts0) : dom Delta0 = domF Fs := by
  induction h with
  | nil => rfl
  | funnel _ _ ih => simp only [dom, List.map_cons]; rw [show List.map Bound.X _ = dom _ from rfl, ih]; simp [domF]
  | ground _ ih => rw [ih]; simp [domF]

theorem Pairing.sub {Delta : Bounds} {Fs : List Funnel} {Ts : List Ty} {Delta0 : Bounds} {Ts0 : List Ty}
    (h : Pairing Delta Fs Ts Delta0 Ts0) : Sub1 Delta0 Delta := by
  induction h with
  | nil => intro _ hx; cases hx
  | funnel hm _ ih =>
    intro b hb
    cases hb with
    | head => exact hm
    | tail _ hb => exact ih b hb
  | ground _ ih => exact ih

theorem bound_unique {Delta : Bounds} (hn : (dom Delta).Nodup) {X : TVarName} {T1 T2 : Ty}
    (h1 : List.Mem { X := X, T := T1 } Delta) (h2 : List.Mem { X := X, T := T2 } Delta) : T1 = T2 := by
  have := nodup_map_inj hn h1 h2 rfl
  simp only [Bound.mk.injEq] at this
  exact this.2

theorem Pairing.unique {Delta : Bounds} (hn : (dom Delta).Nodup) {Fs : List Funnel} {Ts : List Ty}
    {D1 : Bounds} {T1 : List Ty} (h1 : Pairing Delta Fs Ts D1 T1) :
    forall {Ts' : List Ty} {D2 : Bounds} {T2 : List Ty}, Pairing Delta Fs Ts' D2 T2 -> D1 = D2 := by
  induction h1 with
  | nil => intro _ _ _ h2; cases h2; rfl
  | funnel hm _ ih =>
    intro _ _ _ h2
    cases h2 with
    | funnel hm2 h2' => rw [bound_unique hn hm hm2, ih h2']
  | ground _ ih =>
    intro _ _ _ h2
    cases h2 with
    | ground h2' => exact ih h2'

theorem abs_funnels {Fs : List Funnel} (h : forall F, List.Mem F Fs -> F.isFunnel = true) :
    abs Fs = vars (domF Fs) := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih =>
    have ih' := ih (fun F' hF' => h F' (List.Mem.tail _ hF'))
    cases F with
    | ground G => have := h _ (List.Mem.head _); simp [Funnel.isFunnel] at this
    | funnel X =>
      simp only [abs, List.map_cons, Funnel.abs, domF, List.filterMap_cons, vars] at ih' |-
      rw [ih']

end Funnelling
