import Funnelling.Sound.Decomp

open Funnelling.SoundSimp

namespace Funnelling

section
variable {A B : Type} [DecidableEq A]

theorem lookup_cons_eq {a : A} {b : B} {r : List (Prod A B)} : List.lookup a ((a, b) :: r) = some b := by
  simp [List.lookup]

theorem lookup_cons_ne {a x : A} {b : B} {r : List (Prod A B)} (h : Not (x = a)) :
    List.lookup x ((a, b) :: r) = List.lookup x r := by
  have hb : (x == a) = false := by simp [h]
  simp [List.lookup, hb]

theorem lookup_mem {x : A} {y : B} : forall {r : List (Prod A B)}, List.lookup x r = some y ->
    List.Mem (x, y) r
  | [], h => by simp [List.lookup] at h
  | (a, b) :: r, h => by
    by_cases hx : x = a
    . subst hx; rw [lookup_cons_eq] at h; cases h; exact List.Mem.head _
    . rw [lookup_cons_ne hx] at h; exact List.Mem.tail _ (lookup_mem h)

theorem lookup_none {x : A} : forall {r : List (Prod A B)}, (forall p, List.Mem p r -> Not (p.1 = x)) ->
    List.lookup x r = none
  | [], _ => rfl
  | (a, b) :: r, h => by
    have hx : Not (x = a) := fun e => h (a, b) (List.Mem.head _) e.symm
    rw [lookup_cons_ne hx]
    exact lookup_none (fun p hp => h p (List.Mem.tail _ hp))

theorem lookup_isSome {x : A} : forall {r : List (Prod A B)}, List.Mem x (r.map Prod.fst) ->
    exists y, List.lookup x r = some y
  | [], h => by cases h
  | (a, b) :: r, h => by
    by_cases hx : x = a
    . subst hx; exact Exists.intro b lookup_cons_eq
    . rw [lookup_cons_ne hx]
      cases h with
      | head => exact absurd rfl hx
      | tail _ h => exact lookup_isSome h

theorem lookup_append_left {x : A} : forall {r1 r2 : List (Prod A B)}, List.Mem x (r1.map Prod.fst) ->
    List.lookup x (r1 ++ r2) = List.lookup x r1
  | [], _, h => by cases h
  | (a, b) :: r1, r2, h => by
    by_cases hx : x = a
    . subst hx; simp [List.lookup]
    . rw [List.cons_append, lookup_cons_ne hx, lookup_cons_ne hx]
      cases h with
      | head => exact absurd rfl hx
      | tail _ h => exact lookup_append_left h

omit [DecidableEq A] in theorem zip_map_fst : forall {xs : List A} {ys : List B}, xs.length = ys.length -> (xs.zip ys).map Prod.fst = xs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact zip_map_fst (by simpa using h)

end

section
variable {A : Type} [DecidableEq A]

def rn (r : List (Prod A A)) (x : A) : A := (List.lookup x r).getD x

theorem rn_cons_eq {a b : A} {r : List (Prod A A)} : rn ((a, b) :: r) a = b := by simp [rn]

theorem rn_cons_ne {a b x : A} {r : List (Prod A A)} (h : Not (x = a)) : rn ((a, b) :: r) x = rn r x := by
  simp [rn, lookup_cons_ne h]

theorem rn_nil {x : A} : rn ([] : List (Prod A A)) x = x := rfl

theorem rn_id : forall {r : List (Prod A A)}, (forall p, List.Mem p r -> p.1 = p.2) -> forall x, rn r x = x
  | [], _, _ => rfl
  | (a, b) :: r, h, x => by
    by_cases hx : x = a
    . subst hx; rw [rn_cons_eq]; exact (h (x, b) (List.Mem.head _)).symm
    . rw [rn_cons_ne hx]; exact rn_id (fun p hp => h p (List.Mem.tail _ hp)) x

theorem rn_zip_mem : forall {xs ys : List A} {r : List (Prod A A)} {x : A}, xs.length = ys.length ->
    List.Mem x xs -> List.Mem (rn (xs.zip ys ++ r) x) ys
  | [], [], _, _, _, h => by cases h
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | a :: xs, b :: ys, r, x, hl, hx => by
    simp only [List.zip_cons_cons, List.cons_append]
    by_cases h : x = a
    . subst h; rw [rn_cons_eq]; exact List.Mem.head _
    . rw [rn_cons_ne h]
      cases hx with
      | head => exact absurd rfl h
      | tail _ hx => exact List.Mem.tail _ (rn_zip_mem (by simpa using hl) hx)

theorem rn_zip_not_mem : forall {xs ys : List A} {r : List (Prod A A)} {x : A},
    Not (List.Mem x xs) -> rn (xs.zip ys ++ r) x = rn r x
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | a :: xs, b :: ys, r, x, hx => by
    simp only [List.zip_cons_cons, List.cons_append]
    have h : Not (x = a) := fun e => hx (by rw [e]; exact List.Mem.head _)
    rw [rn_cons_ne h]
    exact rn_zip_not_mem (fun h' => hx (List.Mem.tail _ h'))

theorem rn_zip_comp : forall {xs ys zs : List A} {r1 r2 r3 : List (Prod A A)} {x : A},
    xs.length = ys.length -> ys.length = zs.length -> ys.Nodup -> List.Mem x xs ->
    rn (ys.zip zs ++ r2) (rn (xs.zip ys ++ r1) x) = rn (xs.zip zs ++ r3) x
  | [], _, _, _, _, _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, _, h, _, _ => by simp at h
  | a :: xs, b :: ys, c :: zs, r1, r2, r3, x, h1, h2, hn, hx => by
    simp only [List.zip_cons_cons, List.cons_append]
    by_cases h : x = a
    . subst h; rw [rn_cons_eq, rn_cons_eq, rn_cons_eq]
    . rw [rn_cons_ne h, rn_cons_ne h]
      have hx' : List.Mem x xs := by
        cases hx with
        | head => exact absurd rfl h
        | tail _ hx => exact hx
      have hm := rn_zip_mem (r := r1) (by simpa using h1) hx'
      have hb : Not (rn (xs.zip ys ++ r1) x = b) := by intro e; rw [e] at hm; exact (List.nodup_cons.mp hn).1 hm
      rw [rn_cons_ne hb]
      exact rn_zip_comp (by simpa using h1) (by simpa using h2) (List.nodup_cons.mp hn).2 hx'

end

theorem VarName.ren_eq (rv : VRen) (x : VarName) : x.ren rv = rn rv x := rfl

theorem TVarName.ren_eq (rt : TRen) (X : TVarName) : X.ren rt = rn rt X := rfl

end Funnelling
