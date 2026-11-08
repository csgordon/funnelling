import Funnelling.Sound.Inversion

open Funnelling.SoundSimp

namespace Funnelling.High

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
      right
      exact Exists.intro [] (And.intro (by simpa using h1.2.symm) (by simpa using h1.1.symm))
    | cons y a =>
      left
      simp only [List.cons_append, List.cons.injEq] at h1
      refine Exists.intro a (And.intro ?_ h1.2.2)
      rw [h1.1, h1.2.1]
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

end Funnelling.High