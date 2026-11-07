import Funnelling.Sound.Conv

open Funnelling.SoundSimp

namespace Funnelling.High

mutual
theorem Expr.vbinders_gsubst {s : GSubst} : forall (e : Expr), (e.gsubst s).vbinders = e.vbinders
  | .var _ => rfl
  | .call e _ _ es => by simp only [Expr.gsubst, Expr.vbinders, Expr.vbinders_gsubst e, Expr.vbindersList_gsubst es]
  | .superCall e _ _ _ es => by simp only [Expr.gsubst, Expr.vbinders, Expr.vbinders_gsubst e, Expr.vbindersList_gsubst es]
  | .field e _ => by simp only [Expr.gsubst, Expr.vbinders, Expr.vbinders_gsubst e]
  | .new _ _ es => by simp only [Expr.gsubst, Expr.vbinders, Expr.vbindersList_gsubst es]
  | .newLocal _ _ _ _ es Ms => by
    simp only [Expr.gsubst, Expr.vbinders, Expr.vbindersList_gsubst es, Method.vbindersList_gsubst Ms]
  | .ifInst e0 _ _ e1 e2 => by
    simp only [Expr.gsubst, Expr.vbinders, Expr.vbinders_gsubst e0, Expr.vbinders_gsubst e1, Expr.vbinders_gsubst e2]
theorem Expr.vbindersList_gsubst {s : GSubst} : forall (es : List Expr),
    Expr.vbindersList (Expr.gsubstList s es) = Expr.vbindersList es
  | [] => rfl
  | e :: es => by simp only [Expr.gsubstList, Expr.vbindersList, Expr.vbinders_gsubst e, Expr.vbindersList_gsubst es]
theorem Method.vbinders_gsubst {s : GSubst} : forall (M : Method), (M.gsubst s).vbinders = M.vbinders
  | .mk _ _ _ ps e => by simp only [Method.gsubst, Method.vbinders, Expr.vbinders_gsubst e, names_subst]
theorem Method.vbindersList_gsubst {s : GSubst} : forall (Ms : List Method),
    Method.vbindersList (Method.gsubstList s Ms) = Method.vbindersList Ms
  | [] => rfl
  | M :: Ms => by simp only [Method.gsubstList, Method.vbindersList, Method.vbinders_gsubst M, Method.vbindersList_gsubst Ms]
end

mutual
theorem Expr.vbinders_vsubst {n : VSubst} {x : VarName} : forall {e : Expr}, List.Mem x e.vbinders ->
    List.Mem x (e.vsubst n).vbinders
  | .var _, h => by cases h
  | .call e _ _ es, h => by
    simp only [Expr.vsubst, Expr.vbinders, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . exact Or.inl (Expr.vbinders_vsubst h)
    . exact Or.inr (Expr.vbindersList_vsubst h)
  | .superCall e _ _ _ es, h => by
    simp only [Expr.vsubst, Expr.vbinders, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . exact Or.inl (Expr.vbinders_vsubst h)
    . exact Or.inr (Expr.vbindersList_vsubst h)
  | .field e _, h => by
    simp only [Expr.vsubst, Expr.vbinders] at h |-
    exact Expr.vbinders_vsubst h
  | .new _ _ es, h => by
    simp only [Expr.vsubst, Expr.vbinders] at h |-
    exact Expr.vbindersList_vsubst h
  | .newLocal _ _ _ _ es Ms, h => by
    simp only [Expr.vsubst, Expr.vbinders, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . exact Or.inl (Expr.vbindersList_vsubst h)
    . exact Or.inr (Method.vbindersList_vsubst h)
  | .ifInst e0 _ _ e1 e2, h => by
    simp only [Expr.vsubst, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons] at h |-
    rcases h with ((h | h) | h) | h
    . exact Or.inl (Or.inl (Or.inl h))
    . exact Or.inl (Or.inl (Or.inr (Expr.vbinders_vsubst h)))
    . exact Or.inl (Or.inr (Expr.vbinders_vsubst h))
    . exact Or.inr (Expr.vbinders_vsubst h)
theorem Expr.vbindersList_vsubst {n : VSubst} {x : VarName} : forall {es : List Expr},
    List.Mem x (Expr.vbindersList es) -> List.Mem x (Expr.vbindersList (Expr.vsubstList n es))
  | [], h => by cases h
  | e :: es, h => by
    simp only [Expr.vsubstList, Expr.vbindersList, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . exact Or.inl (Expr.vbinders_vsubst h)
    . exact Or.inr (Expr.vbindersList_vsubst h)
theorem Method.vbinders_vsubst {n : VSubst} {x : VarName} : forall {M : Method}, List.Mem x M.vbinders ->
    List.Mem x (M.vsubst n).vbinders
  | .mk _ _ _ ps e, h => by
    simp only [Method.vsubst, Method.vbinders, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . exact Or.inl h
    . exact Or.inr (Expr.vbinders_vsubst h)
theorem Method.vbindersList_vsubst {n : VSubst} {x : VarName} : forall {Ms : List Method},
    List.Mem x (Method.vbindersList Ms) -> List.Mem x (Method.vbindersList (Method.vsubstList n Ms))
  | [], h => by cases h
  | M :: Ms, h => by
    simp only [Method.vsubstList, Method.vbindersList, listMem_iff, List.mem_append] at h |-
    rcases h with h | h
    . exact Or.inl (Method.vbinders_vsubst h)
    . exact Or.inr (Method.vbindersList_vsubst h)
end

theorem mem_zip_fst {A B : Type} : forall {xs : List A} {ys : List B} {x : A}, xs.length = ys.length ->
    List.Mem x xs -> exists y, List.Mem (x, y) (xs.zip ys)
  | [], _, _, _, h => by cases h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: xs, b :: ys, x, hl, hx => by
    cases hx with
    | head => exact Exists.intro b (List.Mem.head _)
    | tail _ hx =>
      cases mem_zip_fst (by simpa using hl) hx with
      | intro y hy => exact Exists.intro y (List.Mem.tail _ hy)

theorem lookup_zip_ren {A B : Type} [DecidableEq A] {rt : List (Prod A A)} :
    forall {X1 X2 : List A} {Us : List B} {X : A}, X1.length = X2.length -> X2.Nodup ->
    (forall p, List.Mem p (X1.zip X2) -> rn rt p.1 = p.2) -> List.Mem X X1 ->
    List.lookup X (X1.zip Us) = List.lookup (rn rt X) (X2.zip Us)
  | [], _, _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | a :: X1, b :: X2, [], X, _, _, _, _ => by simp [List.lookup]
  | a :: X1, b :: X2, u :: Us, X, hl, hn, hp, hX => by
    simp only [List.zip_cons_cons]
    by_cases e : X = a
    . subst e
      rw [hp (X, b) (List.Mem.head _), lookup_cons_eq, lookup_cons_eq]
    . rw [lookup_cons_ne e]
      have hX' : List.Mem X X1 := by
        cases hX with
        | head => exact absurd rfl e
        | tail _ h => exact h
      have hl' : X1.length = X2.length := by simpa using hl
      have hp' : forall p, List.Mem p (X1.zip X2) -> rn rt p.1 = p.2 := fun p h => hp p (List.Mem.tail _ h)
      have hne : Not (rn rt X = b) := by
        cases mem_zip_fst hl' hX' with
        | intro y hy =>
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
