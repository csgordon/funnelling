import Funnelling.Sound.ReflS

open Funnelling.SoundSimp

namespace Funnelling.High

theorem rn_zip_indep {A : Type} [DecidableEq A] {xs ys : List A} {r1 r2 : List (Prod A A)} {w : A}
    (hl : xs.length = ys.length) (hw : List.Mem w xs) : rn (xs.zip ys ++ r1) w = rn (xs.zip ys ++ r2) w := by
  have hm : List.Mem w ((xs.zip ys).map Prod.fst) := by rw [zip_map_fst hl]; exact hw
  simp only [rn]
  rw [lookup_append_left hm, lookup_append_left hm]

structure VSEnv (rv rvo : VRen) (n1 n2 : VSubst) (S : List VarName) : Prop where
  sv : forall w, List.Mem w S ->
    (exists v, List.lookup w n1 = some v /\ List.lookup (rn rv w) n2 = some v) \/
    (List.lookup w n1 = none /\ List.lookup (rn rv w) n2 = none /\ rn rv w = rn rvo w)
  k : forall p, List.Mem p rv -> Not (p.1 = this) /\ Not (p.2 = this)
  ko : forall p, List.Mem p rvo -> Not (p.1 = this)
  c1 : forall p, List.Mem p n1 -> p.2.expr.closed [] [] = true

abbrev NotDom (xs : List VarName) (n : VSubst) : Prop := forall x, List.Mem x xs -> Not (List.Mem x (n.map Prod.fst))

theorem lookup_none_of_notDom {n : VSubst} {x : VarName} (h : Not (List.Mem x (n.map Prod.fst))) :
    List.lookup x n = none := by
  apply lookup_none
  intro p hp e
  apply h
  rw [<- e]
  exact List.mem_map_of_mem hp

theorem lookup_filter_this {n : VSubst} {w : VarName} (hw : Not (w = this)) :
    List.lookup w (n.filter fun p => p.1 != this) = List.lookup w n := by
  induction n with
  | nil => rfl
  | cons p n ih =>
    by_cases hp : p.1 = this
    . have : (p.1 != this) = false := by simp [hp]
      rw [List.filter_cons_of_neg (by simp [hp]), ih]
      have hne : Not (w = p.1) := fun e => hw (e.trans hp)
      cases p with
      | mk a b => exact (lookup_cons_ne hne).symm
    . rw [List.filter_cons_of_pos (by simpa using hp)]
      cases p with
      | mk a b =>
        by_cases e : w = a
        . subst e; rw [lookup_cons_eq, lookup_cons_eq]
        . rw [lookup_cons_ne e, lookup_cons_ne e, ih]

theorem lookup_filter_this_self {n : VSubst} : List.lookup this (n.filter fun p => p.1 != this) = none := by
  apply lookup_none
  intro p hp e
  have := (List.mem_filter.mp hp).2
  simp [e] at this

theorem VSEnv.ifExt {rv rvo : VRen} {n1 n2 : VSubst} {S : List VarName} (env : VSEnv rv rvo n1 n2 S)
    {x y : VarName} (hx : Not (x = this)) (hy : Not (y = this)) (hx1 : Not (List.Mem x (n1.map Prod.fst)))
    (hy2 : Not (List.Mem y (n2.map Prod.fst))) :
    VSEnv ((x, y) :: rv) ((x, y) :: rvo) n1 n2 (x :: S) where
  sv := by
    intro w hw
    by_cases e : w = x
    . subst e
      rw [rn_cons_eq, rn_cons_eq]
      exact Or.inr (And.intro (lookup_none_of_notDom hx1) (And.intro (lookup_none_of_notDom hy2) rfl))
    . rw [rn_cons_ne e, rn_cons_ne e]
      apply env.sv
      cases hw with
      | head => exact absurd rfl e
      | tail _ h => exact h
  k := by
    intro p hp
    cases hp with
    | head => exact And.intro hx hy
    | tail _ hp => exact env.k p hp
  ko := by
    intro p hp
    cases hp with
    | head => exact hx
    | tail _ hp => exact env.ko p hp
  c1 := env.c1

theorem VSEnv.methExt {rv rvo : VRen} {n1 n2 : VSubst} {S : List VarName} (env : VSEnv rv rvo n1 n2 S)
    {xa xb : List VarName} (hl : xa.length = xb.length) (hta : Not (List.Mem this xa))
    (htb : Not (List.Mem this xb)) (ha1 : NotDom xa n1) (hb2 : NotDom xb n2)
    (hn1 : forall p, List.Mem p n1 -> Not (p.1 = this)) (hn2 : forall p, List.Mem p n2 -> Not (p.1 = this)) :
    VSEnv (xa.zip xb ++ rv) (xa.zip xb ++ rvo) n1 n2 (this :: S ++ xa) where
  sv := by
    intro w hw
    by_cases hm : List.Mem w xa
    . have hmb := rn_zip_mem (r := rv) hl hm
      exact Or.inr (And.intro (lookup_none_of_notDom (ha1 w hm))
        (And.intro (lookup_none_of_notDom (hb2 _ hmb)) (rn_zip_indep hl hm)))
    . rw [rn_zip_not_mem hm, rn_zip_not_mem hm]
      by_cases hwt : w = this
      . subst hwt
        have h1 : rn rv this = this := rn_this (fun p hp => (env.k p hp).1)
        have h2 : rn rvo this = this := rn_this env.ko
        rw [h1, h2]
        exact Or.inr (And.intro (lookup_none (fun p hp e => hn1 p hp e))
          (And.intro (lookup_none (fun p hp e => hn2 p hp e)) rfl))
      . have hwS : List.Mem w S := by
          simp only [listMem_iff, List.mem_append, List.mem_cons] at hw hm
          rcases hw with (h | h) | h
          . exact absurd h hwt
          . exact h
          . exact absurd h hm
        exact env.sv w hwS
  k := by
    intro p hp
    simp only [listMem_iff, List.mem_append] at hp
    rcases hp with hp | hp
    . have h1 := List.of_mem_zip hp
      exact And.intro (fun e => hta (e ▸ h1.1)) (fun e => htb (e ▸ h1.2))
    . exact env.k p hp
  ko := by
    intro p hp
    simp only [listMem_iff, List.mem_append] at hp
    rcases hp with hp | hp
    . exact fun e => hta (e ▸ (List.of_mem_zip hp).1)
    . exact env.ko p hp
  c1 := env.c1

theorem VSEnv.filt {rv rvo : VRen} {n1 n2 : VSubst} {S : List VarName} (env : VSEnv rv rvo n1 n2 S) :
    VSEnv rv rvo (n1.filter fun p => p.1 != this) (n2.filter fun p => p.1 != this) S where
  sv := by
    intro w hw
    by_cases hwt : w = this
    . subst hwt
      have h1 : rn rv this = this := rn_this (fun p hp => (env.k p hp).1)
      have h2 : rn rvo this = this := rn_this env.ko
      rw [h1, h2]
      exact Or.inr (And.intro lookup_filter_this_self (And.intro lookup_filter_this_self rfl))
    . have hne := rn_ne_this (fun p hp => (env.k p hp).2) hwt
      rw [lookup_filter_this hwt, lookup_filter_this hne]
      exact env.sv w hw
  k := env.k
  ko := env.ko
  c1 := fun p hp => env.c1 p (List.mem_filter.mp hp).1

theorem filter_this_no {n : VSubst} : forall p, List.Mem p (n.filter fun p => p.1 != this) -> Not (p.1 = this) := by
  intro p hp e
  have := (List.mem_filter.mp hp).2
  simp [e] at this

theorem notDom_filter {xs : List VarName} {n : VSubst} (h : NotDom xs n) :
    NotDom xs (n.filter fun p => p.1 != this) := by
  intro x hx hm
  apply h x hx
  have := List.mem_map.mp hm
  cases this with
  | intro p hp => rw [<- hp.2]; exact List.mem_map_of_mem (List.mem_filter.mp hp.1).1

theorem notDom_append_left {xs ys : List VarName} {n : VSubst} (h : NotDom (xs ++ ys) n) : NotDom xs n :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem notDom_append_right {xs ys : List VarName} {n : VSubst} (h : NotDom (xs ++ ys) n) : NotDom ys n :=
  fun x hx => h x (List.mem_append_right _ hx)

mutual
theorem RenE.vsub {rv rt a b} : RenE rv rt a b -> forall {rvo n1 n2 S T}, VSEnv rv rvo n1 n2 S ->
    a.closed T S = true -> NotDom a.vbinders n1 -> NotDom b.vbinders n2 -> NoThis a -> NoThis b ->
    RenE rvo rt (a.vsubst n1) (b.vsubst n2)
  | .var (x := x), rvo, n1, n2, S, T, env, hc, _, _, _, _ => by
    simp only [Expr.closed] at hc
    have hx : List.Mem x S := by simpa using hc
    rcases env.sv x hx with h | h
    . cases h with
      | intro v hv =>
        simp only [Expr.vsubst, VarName.ren_eq, hv.1, hv.2]
        exact RenE.value (env.c1 (x, v) (lookup_mem hv.1)) (rn_this env.ko)
    . simp only [Expr.vsubst, VarName.ren_eq, h.1, h.2.1]
      rw [h.2.2]
      exact RenE.var
  | .call h1 hs1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vbinders] at hd1 hd2
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Expr.vsubst]
    exact RenE.call (RenE.vsub h1 env hc.1.1 (notDom_append_left hd1) (notDom_append_left hd2) ha.1 hb.1)
      (RenEs.vsub hs1 env hc.2 (notDom_append_right hd1) (notDom_append_right hd2) ha.2 hb.2)
  | .superCall h1 hs1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vbinders] at hd1 hd2
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Expr.vsubst]
    exact RenE.superCall (RenE.vsub h1 env hc.1.1 (notDom_append_left hd1) (notDom_append_left hd2) ha.1 hb.1)
      (RenEs.vsub hs1 env hc.2 (notDom_append_right hd1) (notDom_append_right hd2) ha.2 hb.2)
  | .field h1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed] at hc
    simp only [Expr.vbinders] at hd1 hd2
    simp only [NoThis, Expr.vbinders] at ha hb
    simp only [Expr.vsubst]
    exact RenE.field (RenE.vsub h1 env hc hd1 hd2 ha hb)
  | .new hs1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vbinders] at hd1 hd2
    simp only [NoThis, Expr.vbinders] at ha hb
    simp only [Expr.vsubst]
    exact RenE.new (RenEs.vsub hs1 env hc.2 hd1 hd2 ha hb)
  | .newLocal hs1 hm1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vbinders] at hd1 hd2
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Expr.vsubst]
    exact RenE.newLocal (RenEs.vsub hs1 env hc.1.2 (notDom_append_left hd1) (notDom_append_left hd2) ha.1 hb.1)
      (RenMs.vsub hm1 env.filt hc.2 (notDom_filter (notDom_append_right hd1))
        (notDom_filter (notDom_append_right hd2)) ha.2 hb.2 filter_this_no filter_this_no)
  | .ifInst h01 h11 h21, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.vbinders] at hd1 hd2
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ha hb
    simp only [Expr.vsubst]
    have hd1' : NotDom (_ ++ _ ++ _) n1 := fun x hx => hd1 x (List.Mem.tail _ hx)
    have hd2' : NotDom (_ ++ _ ++ _) n2 := fun x hx => hd2 x (List.Mem.tail _ hx)
    exact RenE.ifInst
      (RenE.vsub h01 env hc.1.1.1 (notDom_append_left (notDom_append_left hd1'))
        (notDom_append_left (notDom_append_left hd2')) ha.1.1.2 hb.1.1.2)
      (RenE.vsub h11 (env.ifExt (fun e => ha.1.1.1 e.symm) (fun e => hb.1.1.1 e.symm)
          (hd1 _ (List.Mem.head _)) (hd2 _ (List.Mem.head _))) hc.1.2
        (notDom_append_right (notDom_append_left hd1')) (notDom_append_right (notDom_append_left hd2'))
        ha.1.2 hb.1.2)
      (RenE.vsub h21 env hc.2 (notDom_append_right hd1') (notDom_append_right hd2') ha.2 hb.2)
theorem RenEs.vsub {rv rt as bs} : RenEs rv rt as bs -> forall {rvo n1 n2 S T}, VSEnv rv rvo n1 n2 S ->
    Expr.closedList T S as = true -> NotDom (Expr.vbindersList as) n1 -> NotDom (Expr.vbindersList bs) n2 ->
    Not (List.Mem this (Expr.vbindersList as)) -> Not (List.Mem this (Expr.vbindersList bs)) ->
    RenEs rvo rt (Expr.vsubstList n1 as) (Expr.vsubstList n2 bs)
  | .nil, _, _, _, _, _, _, _, _, _, _, _ => RenEs.nil
  | .cons h1 hs1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closedList, Bool.and_eq_true] at hc
    simp only [Expr.vbindersList] at hd1 hd2
    simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Expr.vsubstList]
    exact RenEs.cons (RenE.vsub h1 env hc.1 (notDom_append_left hd1) (notDom_append_left hd2) ha.1 hb.1)
      (RenEs.vsub hs1 env hc.2 (notDom_append_right hd1) (notDom_append_right hd2) ha.2 hb.2)
theorem RenM.vsub {rv rt Ma Mb} : RenM rv rt Ma Mb -> forall {rvo n1 n2 S T}, VSEnv rv rvo n1 n2 S ->
    Ma.closed T S = true -> NotDom Ma.vbinders n1 -> NotDom Mb.vbinders n2 -> NoThisM Ma -> NoThisM Mb ->
    (forall p, List.Mem p n1 -> Not (p.1 = this)) -> (forall p, List.Mem p n2 -> Not (p.1 = this)) ->
    RenM rvo rt (Ma.vsubst n1) (Mb.vsubst n2)
  | .mk (ps := ps) (xs' := xs) hL hl h1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb, hn1, hn2 => by
    simp only [Method.closed, Bool.and_eq_true] at hc
    simp only [Method.vbinders] at hd1 hd2
    simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    rw [names_renParams hl] at hd2 hb
    simp only [Method.vsubst]
    have hla : (ps.map VarDecl.x).length = xs.length := by simp [hl]
    exact RenM.mk hL hl (RenE.vsub h1 (env.methExt hla ha.1 hb.1 (notDom_append_left hd1)
      (notDom_append_left hd2) hn1 hn2) hc.2 (notDom_append_right hd1) (notDom_append_right hd2) ha.2 hb.2)
theorem RenMs.vsub {rv rt Mas Mbs} : RenMs rv rt Mas Mbs -> forall {rvo n1 n2 S T}, VSEnv rv rvo n1 n2 S ->
    Method.closedList T S Mas = true -> NotDom (Method.vbindersList Mas) n1 ->
    NotDom (Method.vbindersList Mbs) n2 ->
    Not (List.Mem this (Method.vbindersList Mas)) -> Not (List.Mem this (Method.vbindersList Mbs)) ->
    (forall p, List.Mem p n1 -> Not (p.1 = this)) -> (forall p, List.Mem p n2 -> Not (p.1 = this)) ->
    RenMs rvo rt (Method.vsubstList n1 Mas) (Method.vsubstList n2 Mbs)
  | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => RenMs.nil
  | .cons h1 hs1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb, hn1, hn2 => by
    simp only [Method.closedList, Bool.and_eq_true] at hc
    simp only [Method.vbindersList] at hd1 hd2
    simp only [Method.vbindersList, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Method.vsubstList]
    exact RenMs.cons (RenM.vsub h1 env hc.1 (notDom_append_left hd1) (notDom_append_left hd2) ha.1 hb.1 hn1 hn2)
      (RenMs.vsub hs1 env hc.2 (notDom_append_right hd1) (notDom_append_right hd2) ha.2 hb.2 hn1 hn2)
end

end Funnelling.High