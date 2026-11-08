import Funnelling.Sound.Conv

open Funnelling.SoundSimp

namespace Funnelling.High

mutual
theorem Expr.gsubst_keeps {s : GSubst} : forall (e : Expr), (e.gsubst s).vbinders = e.vbinders /\
    (e.gsubst s).ifVars = e.ifVars /\ (e.gsubst s).tbinders = e.tbinders /\ (e.gsubst s).uniq = e.uniq /\
    forall Xs xs, (e.gsubst s).noShadow Xs xs = e.noShadow Xs xs
  | .var _ => ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | .call e _ _ es => by
    simp only [Expr.gsubst, Expr.vbinders, Expr.ifVars, Expr.tbinders, Expr.uniq, Expr.noShadow, Expr.gsubst_keeps e,
      Expr.gsubstList_keeps es, implies_true, and_self]
  | .superCall e _ _ _ es => by
    simp only [Expr.gsubst, Expr.vbinders, Expr.ifVars, Expr.tbinders, Expr.uniq, Expr.noShadow, Expr.gsubst_keeps e,
      Expr.gsubstList_keeps es, implies_true, and_self]
  | .field e _ => by
    simp only [Expr.gsubst, Expr.vbinders, Expr.ifVars, Expr.tbinders, Expr.uniq, Expr.noShadow, Expr.gsubst_keeps e,
      implies_true, and_self]
  | .new _ _ es => by
    simp only [Expr.gsubst, Expr.vbinders, Expr.ifVars, Expr.tbinders, Expr.uniq, Expr.noShadow,
      Expr.gsubstList_keeps es, implies_true, and_self]
  | .newLocal _ _ _ _ es Ms => by
    simp only [Expr.gsubst, Expr.vbinders, Expr.ifVars, Expr.tbinders, Expr.uniq, Expr.noShadow,
      Expr.gsubstList_keeps es, Method.gsubstList_keeps Ms, implies_true, and_self]
  | .ifInst e0 _ _ e1 e2 => by
    simp only [Expr.gsubst, Expr.vbinders, Expr.ifVars, Expr.tbinders, Expr.uniq, Expr.noShadow, Expr.gsubst_keeps e0,
      Expr.gsubst_keeps e1, Expr.gsubst_keeps e2, implies_true, and_self]
theorem Expr.gsubstList_keeps {s : GSubst} : forall (es : List Expr),
    Expr.vbindersList (Expr.gsubstList s es) = Expr.vbindersList es /\
    Expr.ifVarsList (Expr.gsubstList s es) = Expr.ifVarsList es /\
    Expr.tbindersList (Expr.gsubstList s es) = Expr.tbindersList es /\
    Expr.uniqList (Expr.gsubstList s es) = Expr.uniqList es /\
    forall Xs xs, Expr.noShadowList Xs xs (Expr.gsubstList s es) = Expr.noShadowList Xs xs es
  | [] => ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | e :: es => by
    simp only [Expr.gsubstList, Expr.vbindersList, Expr.ifVarsList, Expr.tbindersList, Expr.uniqList,
      Expr.noShadowList, Expr.gsubst_keeps e, Expr.gsubstList_keeps es, implies_true, and_self]
theorem Method.gsubst_keeps {s : GSubst} : forall (M : Method), (M.gsubst s).vbinders = M.vbinders /\
    (M.gsubst s).ifVars = M.ifVars /\ (M.gsubst s).tbinders = M.tbinders /\ (M.gsubst s).uniq = M.uniq /\
    forall Xs xs, (M.gsubst s).noShadow Xs xs = M.noShadow Xs xs
  | .mk _ _ _ _ e => by
    simp only [Method.gsubst, Method.vbinders, Method.ifVars, Method.tbinders, Method.uniq, Method.noShadow,
      dom_bounds_subst, names_subst, Expr.gsubst_keeps e, implies_true, and_self]
theorem Method.gsubstList_keeps {s : GSubst} : forall (Ms : List Method),
    Method.vbindersList (Method.gsubstList s Ms) = Method.vbindersList Ms /\
    Method.ifVarsList (Method.gsubstList s Ms) = Method.ifVarsList Ms /\
    Method.tbindersList (Method.gsubstList s Ms) = Method.tbindersList Ms /\
    Method.uniqList (Method.gsubstList s Ms) = Method.uniqList Ms /\
    forall Xs xs, Method.noShadowList Xs xs (Method.gsubstList s Ms) = Method.noShadowList Xs xs Ms
  | [] => ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | M :: Ms => by
    simp only [Method.gsubstList, Method.vbindersList, Method.ifVarsList, Method.tbindersList, Method.uniqList,
      Method.noShadowList, Method.gsubst_keeps M, Method.gsubstList_keeps Ms, implies_true, and_self]
end

theorem Expr.vbinders_gsubst {s : GSubst} (e : Expr) : (e.gsubst s).vbinders = e.vbinders := (Expr.gsubst_keeps e).1
theorem Expr.ifVars_gsubst {s : GSubst} (e : Expr) : (e.gsubst s).ifVars = e.ifVars := (Expr.gsubst_keeps e).2.1
theorem Expr.tbinders_gsubst {s : GSubst} (e : Expr) : (e.gsubst s).tbinders = e.tbinders := (Expr.gsubst_keeps e).2.2.1
theorem Expr.uniq_gsubst {s : GSubst} (e : Expr) : (e.gsubst s).uniq = e.uniq := (Expr.gsubst_keeps e).2.2.2.1
theorem Expr.noShadow_gsubst {s : GSubst} (e : Expr) {Xs : List TVarName} {xs : List VarName} :
    (e.gsubst s).noShadow Xs xs = e.noShadow Xs xs := (Expr.gsubst_keeps e).2.2.2.2 Xs xs
theorem Method.vbinders_gsubst {s : GSubst} (M : Method) : (M.gsubst s).vbinders = M.vbinders :=
  (Method.gsubst_keeps M).1
theorem Method.uniq_gsubst {s : GSubst} (M : Method) : (M.gsubst s).uniq = M.uniq := (Method.gsubst_keeps M).2.2.2.1
theorem Method.noShadow_gsubst {s : GSubst} (M : Method) {Xs : List TVarName} {xs : List VarName} :
    (M.gsubst s).noShadow Xs xs = M.noShadow Xs xs := (Method.gsubst_keeps M).2.2.2.2 Xs xs

mutual
theorem Expr.vsubst_back : forall (e : Expr) (n : VSubst),
    (forall x, Membership.mem e.vbinders x -> Membership.mem (e.vsubst n).vbinders x) /\ ((e.vsubst n).uniq -> e.uniq) /\
    forall Xs xs, (e.vsubst n).noShadow Xs xs = true -> e.noShadow Xs xs = true
  | .var _, _ => ⟨fun _ h => (nomatch h), fun _ => trivial, fun _ _ _ => rfl⟩
  | .call e _ _ es, n => by
    have h1 := Expr.vsubst_back e n
    have h2 := Expr.vsubstList_back es n
    grind [Expr.vsubst, Expr.vbinders, Expr.uniq, Expr.noShadow]
  | .superCall e _ _ _ es, n => by
    have h1 := Expr.vsubst_back e n
    have h2 := Expr.vsubstList_back es n
    grind [Expr.vsubst, Expr.vbinders, Expr.uniq, Expr.noShadow]
  | .field e _, n => by
    have h1 := Expr.vsubst_back e n
    grind [Expr.vsubst, Expr.vbinders, Expr.uniq, Expr.noShadow]
  | .new _ _ es, n => by
    have h1 := Expr.vsubstList_back es n
    grind [Expr.vsubst, Expr.vbinders, Expr.uniq, Expr.noShadow]
  | .newLocal _ _ _ _ es Ms, n => by
    have h1 := Expr.vsubstList_back es n
    have h2 := Method.vsubstList_back Ms (n.filter fun p => p.1 != this)
    grind [Expr.vsubst, Expr.vbinders, Expr.uniq, Expr.noShadow]
  | .ifInst e0 _ _ e1 e2, n => by
    have h1 := Expr.vsubst_back e0 n
    have h2 := Expr.vsubst_back e1 n
    have h3 := Expr.vsubst_back e2 n
    grind [Expr.vsubst, Expr.vbinders, Expr.uniq, Expr.noShadow]
theorem Expr.vsubstList_back : forall (es : List Expr) (n : VSubst),
    (forall x, Membership.mem (Expr.vbindersList es) x -> Membership.mem (Expr.vbindersList (Expr.vsubstList n es)) x) /\
    (Expr.uniqList (Expr.vsubstList n es) -> Expr.uniqList es) /\
    forall Xs xs, Expr.noShadowList Xs xs (Expr.vsubstList n es) = true -> Expr.noShadowList Xs xs es = true
  | [], _ => ⟨fun _ h => (nomatch h), fun _ => trivial, fun _ _ _ => rfl⟩
  | e :: es, n => by
    have h1 := Expr.vsubst_back e n
    have h2 := Expr.vsubstList_back es n
    grind [Expr.vsubstList, Expr.vbindersList, Expr.uniqList, Expr.noShadowList]
theorem Method.vsubst_back : forall (M : Method) (n : VSubst),
    (forall x, Membership.mem M.vbinders x -> Membership.mem (M.vsubst n).vbinders x) /\ ((M.vsubst n).uniq -> M.uniq) /\
    forall Xs xs, (M.vsubst n).noShadow Xs xs = true -> M.noShadow Xs xs = true
  | .mk _ _ _ _ e, n => by
    have h1 := Expr.vsubst_back e n
    grind [Method.vsubst, Method.vbinders, Method.uniq, Method.noShadow]
theorem Method.vsubstList_back : forall (Ms : List Method) (n : VSubst),
    (forall x, Membership.mem (Method.vbindersList Ms) x -> Membership.mem (Method.vbindersList (Method.vsubstList n Ms)) x) /\
    (Method.uniqList (Method.vsubstList n Ms) -> Method.uniqList Ms) /\
    forall Xs xs, Method.noShadowList Xs xs (Method.vsubstList n Ms) = true -> Method.noShadowList Xs xs Ms = true
  | [], _ => ⟨fun _ h => (nomatch h), fun _ => trivial, fun _ _ _ => rfl⟩
  | M :: Ms, n => by
    have h1 := Method.vsubst_back M n
    have h2 := Method.vsubstList_back Ms n
    grind [Method.vsubstList, Method.vbindersList, Method.uniqList, Method.noShadowList]
end

theorem mem_zip_fst {A B : Type} : forall {xs : List A} {ys : List B} {x : A}, xs.length = ys.length ->
    List.Mem x xs -> exists y, List.Mem (x, y) (xs.zip ys)
  | [], _, _, _, h => by cases h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: xs, b :: ys, x, hl, hx => by
    cases hx with
    | head => exact Exists.intro b (List.Mem.head _)
    | tail _ hx =>
      rcases mem_zip_fst (by simpa using hl) hx with ⟨y, hy⟩; exact Exists.intro y (List.Mem.tail _ hy)

theorem lookup_zip_ren {A B : Type} [DecidableEq A] {rt : List (Prod A A)} :
    forall {X1 X2 : List A} {Us : List B} {X : A}, X1.length = X2.length -> X2.Nodup ->
    (forall p, List.Mem p (X1.zip X2) -> rn rt p.1 = p.2) -> List.Mem X X1 ->
    List.lookup X (X1.zip Us) = List.lookup (rn rt X) (X2.zip Us)
  | [], _, _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | a :: X1, b :: X2, [], X, _, _, _, _ => by simp
  | a :: X1, b :: X2, u :: Us, X, hl, hn, hp, hX => by
    simp only [List.zip_cons_cons]
    by_cases e : X = a
    . simp_all
    . rw [lookup_cons_ne e]
      have hX' : List.Mem X X1 := by
        cases hX with
        | head => exact absurd rfl e
        | tail _ h => exact h
      have hl' : X1.length = X2.length := by simpa using hl
      have hp' : forall p, List.Mem p (X1.zip X2) -> rn rt p.1 = p.2 := fun p h => hp p (List.Mem.tail _ h)
      have hne : Not (rn rt X = b) := by
        rcases mem_zip_fst hl' hX' with ⟨y, hy⟩
        rw [hp' (X, y) hy]
        intro eb
        have eb' : y = b := eb
        rw [eb'] at hy
        exact (List.nodup_cons.mp hn).1 (List.of_mem_zip hy).2
      rw [lookup_cons_ne hne]
      exact lookup_zip_ren hl' (List.nodup_cons.mp hn).2 hp' hX'

theorem rn_zip_pair {A : Type} [DecidableEq A] : forall {xs ys : List A} {r : List (Prod A A)} {x y : A},
    xs.Nodup -> List.Mem (x, y) (xs.zip ys) -> rn (xs.zip ys ++ r) x = y
  | [], _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, _, h => by cases h
  | a :: xs, b :: ys, r, x, y, hn, h => by
    simp only [List.zip_cons_cons, List.cons_append]
    cases h with
    | head => exact rn_cons_eq
    | tail _ h =>
      have hx : Not (x = a) := by
        intro e; subst e
        exact (List.nodup_cons.mp hn).1 (List.of_mem_zip h).1
      rw [rn_cons_ne hx]
      exact rn_zip_pair (List.nodup_cons.mp hn).2 h

theorem zip_self_eq {A : Type} : forall {xs : List A} {p : Prod A A}, List.Mem p (xs.zip xs) -> p.1 = p.2
  | [], _, h => by cases h
  | a :: xs, p, h => by
    simp only [List.zip_cons_cons] at h
    cases h with
    | head => rfl
    | tail _ h => exact zip_self_eq h

theorem RenM.body {rv : VRen} {rt : TRen} {D1 D2 : Bounds} {T1 T2 : Ty} {m1 m2 : MethName}
    {p1 p2 : List VarDecl} {e1 e2 : Expr} (h : RenM rv rt (.mk D1 T1 m1 p1 e1) (.mk D2 T2 m2 p2 e2)) :
    RenE ((p1.map VarDecl.x).zip (p2.map VarDecl.x) ++ rv) ((dom D1).zip (dom D2) ++ rt) e1 e2 /\
      D2.length = D1.length /\ p2.length = p1.length /\ m1 = m2 := by
  cases h with
  | mk hL hl hb =>
    rw [dom_renBounds hL, names_renParams hl]
    exact And.intro hb (And.intro (by simp [hL]) (And.intro (by simp [hl]) rfl))

theorem nodup_append_left {A : Type} {l1 l2 : List A} (h : (l1 ++ l2).Nodup) : l1.Nodup :=
  (List.nodup_append.mp h).1

theorem nodup_append_right {A : Type} {l1 l2 : List A} (h : (l1 ++ l2).Nodup) : l2.Nodup :=
  (List.nodup_append.mp h).2.1

theorem nodup_append_disj {A : Type} {l1 l2 : List A} (h : (l1 ++ l2).Nodup) {x : A} (h1 : List.Mem x l1)
    (h2 : List.Mem x l2) : False := by
  have := (List.nodup_append.mp h).2.2 x h1 x h2
  exact this rfl

end Funnelling.High
