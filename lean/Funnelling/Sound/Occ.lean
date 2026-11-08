import Funnelling.Sound.Chain

open Funnelling.SoundSimp

namespace Funnelling

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
          | exact ih (noShadowList_mem mem_mid h) | exact ih (noShadowList_mem mem_mid h.1)
          | exact ih (noShadowList_mem mem_mid h.2)

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