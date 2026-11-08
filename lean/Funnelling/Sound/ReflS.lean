import Funnelling.Sound.Comp

open Funnelling.SoundSimp

namespace Funnelling.High

theorem rn_zip_self {A : Type} [DecidableEq A] : forall {xs : List A} {r : List (Prod A A)} {w : A},
    List.Mem w xs -> rn (xs.zip xs ++ r) w = w
  | [], _, _, h => by cases h
  | a :: xs, r, w, h => by
    simp only [List.zip_cons_cons, List.cons_append]
    by_cases e : w = a
    . subst e; exact rn_cons_eq
    . rw [rn_cons_ne e]
      cases h with
      | head => exact absurd rfl e
      | tail _ h => exact rn_zip_self h

theorem rn_zip_self_or {A : Type} [DecidableEq A] {xs : List A} {r : List (Prod A A)} {w : A}
    (h : Not (List.Mem w xs) -> rn r w = w) : rn (xs.zip xs ++ r) w = w := by
  by_cases hm : List.Mem w xs
  . exact rn_zip_self hm
  . rw [rn_zip_not_mem hm]; exact h hm

theorem bounds_zip_dom_ren {rt : TRen} : forall {Delta : Bounds},
    (forall b, List.Mem b Delta -> b.T.ren rt = b.T) ->
    (Delta.zip (dom Delta)).map (fun p => ({ X := p.2, T := p.1.T.ren rt } : Bound)) = Delta
  | [], _ => rfl
  | b :: Delta, h => by
    simp only [dom, List.map_cons, List.zip_cons_cons]
    rw [h b (List.Mem.head _),
      show List.map Bound.X Delta = dom Delta from rfl,
      bounds_zip_dom_ren (fun b' hb' => h b' (List.Mem.tail _ hb'))]

theorem params_zip_names_ren {rt : TRen} : forall {ps : List VarDecl},
    (forall p, List.Mem p ps -> p.T.ren rt = p.T) ->
    (ps.zip (ps.map VarDecl.x)).map (fun p => ({ T := p.1.T.ren rt, x := p.2 } : VarDecl)) = ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [List.map_cons, List.zip_cons_cons]
    rw [h p (List.Mem.head _), params_zip_names_ren (fun p' hp' => h p' (List.Mem.tail _ hp'))]

mutual
theorem RenE.reflS {rv : VRen} {rt : TRen} : forall {e : Expr} {Ts : List TVarName} {xs : List VarName},
    e.closed Ts xs = true -> (forall w, (List.Mem w xs \/ w = this) -> rn rv w = w) ->
    (forall X, List.Mem X Ts -> rn rt X = X) -> RenE rv rt e e
  | .var x, Ts, xs, hc, hv, _ => by
    simp only [Expr.closed] at hc
    have hx : List.Mem x xs := by simpa using hc
    have := RenE.var (rv := rv) (rt := rt) (x := x)
    rwa [VarName.ren_eq, hv x (Or.inl hx)] at this
  | .call e Ts' m es, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have := RenE.call (m := m) (Ts := Ts') (RenE.reflS hc.1.1 hv ht) (RenEs.reflS hc.2 hv ht)
    rwa [Ty.renList_id (fun X hX => ht X (all_contains_iff.mp hc.1.2 X hX))] at this
  | .superCall e T Ts' m es, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have h2 := all_contains_iff.mp hc.1.2
    have := RenE.superCall (m := m) (T := T) (Ts := Ts') (RenE.reflS hc.1.1 hv ht) (RenEs.reflS hc.2 hv ht)
    rwa [Ty.renList_id (fun X hX => ht X (h2 X (List.mem_append_right _ hX))),
      Ty.ren_id (fun X hX => ht X (h2 X (List.mem_append_left _ hX)))] at this
  | .field e f, Ts, xs, hc, hv, ht => RenE.field (RenE.reflS hc hv ht)
  | .new C Ts' es, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have := RenE.new (C := C) (Ts := Ts') (RenEs.reflS hc.2 hv ht)
    rwa [Ty.renList_id (fun X hX => ht X (all_contains_iff.mp hc.1 X hX))] at this
  | .newLocal C Fs C' Ts' es Ms, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have h1 := all_contains_iff.mp hc.1.1
    have := RenE.newLocal (C := C) (Fs := Fs) (C' := C') (Ts := Ts') (RenEs.reflS hc.1.2 hv ht)
      (RenMs.reflS hc.2 hv ht)
    rwa [Ty.renList_id (fun X hX => ht X (h1 X (List.mem_append_right _ hX))),
      Funnels.ren_id (fun X hX => ht X (h1 X (List.mem_append_left _ hX)))] at this
  | .ifInst e0 T x e1 e2, Ts, xs, hc, hv, ht => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have hv' : forall w, (List.Mem w (x :: xs) \/ w = this) -> rn ((x, x) :: rv) w = w := by
      intro w hw
      by_cases e : w = x
      . subst e; exact rn_cons_eq
      . rw [rn_cons_ne e]
        apply hv
        rcases hw with hw | hw
        . simp_all
        . exact Or.inr hw
    have := RenE.ifInst (T := T) (y := x) (RenE.reflS hc.1.1.1 hv ht) (RenE.reflS hc.1.2 hv' ht)
      (RenE.reflS hc.2 hv ht)
    rwa [Ty.ren_id (fun X hX => ht X (all_contains_iff.mp hc.1.1.2 X hX))] at this
theorem RenEs.reflS {rv : VRen} {rt : TRen} : forall {es : List Expr} {Ts : List TVarName} {xs : List VarName},
    Expr.closedList Ts xs es = true -> (forall w, (List.Mem w xs \/ w = this) -> rn rv w = w) ->
    (forall X, List.Mem X Ts -> rn rt X = X) -> RenEs rv rt es es
  | [], _, _, _, _, _ => RenEs.nil
  | e :: es, Ts, xs, hc, hv, ht => by
    simp only [Expr.closedList, Bool.and_eq_true] at hc
    exact RenEs.cons (RenE.reflS hc.1 hv ht) (RenEs.reflS hc.2 hv ht)
theorem RenM.reflS {rv : VRen} {rt : TRen} : forall {M : Method} {Ts : List TVarName} {xs : List VarName},
    M.closed Ts xs = true -> (forall w, (List.Mem w xs \/ w = this) -> rn rv w = w) ->
    (forall X, List.Mem X Ts -> rn rt X = X) -> RenM rv rt M M
  | .mk Delta T0 m ps e, Ts, xs, hc, hv, ht => by
    simp only [Method.closed, Bool.and_eq_true] at hc
    have hall := all_contains_iff.mp hc.1
    have ht' : forall X, List.Mem X (Ts ++ dom Delta) -> rn ((dom Delta).zip (dom Delta) ++ rt) X = X := by
      intro X hX
      apply rn_zip_self_or
      intro hn
      exact (List.mem_append.mp hX).elim (ht X) (fun hX => absurd hX hn)
    have hv' : forall w, (List.Mem w (this :: xs ++ ps.map VarDecl.x) \/ w = this) ->
        rn ((ps.map VarDecl.x).zip (ps.map VarDecl.x) ++ rv) w = w := by
      intro w hw
      apply rn_zip_self_or
      intro hn
      apply hv
      simp only [listMem_iff, List.mem_append, List.mem_cons] at hw hn
      rcases hw with ((hw | hw) | hw) | hw
      . exact Or.inr hw
      . exact Or.inl hw
      . exact absurd hw hn
      . exact Or.inr hw
    have h := RenM.mk (rv := rv) (rt := rt) (Delta := Delta) (T0 := T0) (m := m) (ps := ps)
      (Xs' := dom Delta) (xs' := ps.map VarDecl.x) (by simp [dom]) (by simp)
      (RenE.reflS hc.2 hv' ht')
    have hty : forall T : Ty, (forall X, List.Mem X T.ftv -> List.Mem X (Ty.ftvList (T0 :: cod Delta ++ ps.map VarDecl.T))) ->
        T.ren ((dom Delta).zip (dom Delta) ++ rt) = T :=
      fun T hT => Ty.ren_id (fun X hX => ht' X (hall X (hT X hX)))
    rw [hty T0 (fun X hX => by simp only [List.cons_append]; exact List.mem_append_left _ hX),
      bounds_zip_dom_ren (fun b hb => hty b.T (fun X hX => by
        simp only [List.cons_append, Ty.ftvList]
        exact List.mem_append_right _ (by rw [ftvList_append]; exact List.mem_append_left _ (ftvList_map_mem (f := Bound.T) hb hX)))),
      params_zip_names_ren (fun p hp => hty p.T (fun X hX => by
        simp only [List.cons_append, Ty.ftvList]
        exact List.mem_append_right _ (by rw [ftvList_append]; exact List.mem_append_right _ (ftvList_map_mem (f := VarDecl.T) hp hX))))] at h
    exact h
theorem RenMs.reflS {rv : VRen} {rt : TRen} : forall {Ms : List Method} {Ts : List TVarName} {xs : List VarName},
    Method.closedList Ts xs Ms = true -> (forall w, (List.Mem w xs \/ w = this) -> rn rv w = w) ->
    (forall X, List.Mem X Ts -> rn rt X = X) -> RenMs rv rt Ms Ms
  | [], _, _, _, _, _ => RenMs.nil
  | M :: Ms, Ts, xs, hc, hv, ht => by
    simp only [Method.closedList, Bool.and_eq_true] at hc
    exact RenMs.cons (RenM.reflS hc.1 hv ht) (RenMs.reflS hc.2 hv ht)
end

theorem RenE.value {rv : VRen} {rt : TRen} {v : Value} (hc : v.expr.closed [] [] = true)
    (ht : rn rv this = this) : RenE rv rt v.expr v.expr :=
  RenE.reflS hc (fun w hw => by
    rcases hw with hw | hw
    . cases hw
    . subst hw; exact ht) (fun X hX => by cases hX)

end Funnelling.High
