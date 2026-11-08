import Funnelling.Sound.Renaming

open Funnelling.SoundSimp

namespace Funnelling

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
    exact (List.mem_append.mp hp).elim (fun hp => fun e => hta (e ▸ (List.of_mem_zip hp).1)) (env.ko p)
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
  rcases this with ⟨p, hp⟩; rw [<- hp.2]; exact List.mem_map_of_mem (List.mem_filter.mp hp.1).1

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
    . rcases h with ⟨v, hv⟩
      simp only [Expr.vsubst, VarName.ren_eq, hv.1, hv.2]
      exact RenE.value (env.c1 (x, v) (lookup_mem hv.1)) (rn_this env.ko)
    . simp only [Expr.vsubst, VarName.ren_eq, h.1, h.2.1]
      rw [h.2.2]
      exact RenE.var
  | .call h1 hs1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    exact RenE.call (RenE.vsub h1 env hc.1.1 (notDom_append_left hd1) (notDom_append_left hd2) ha.1 hb.1)
      (RenEs.vsub hs1 env hc.2 (notDom_append_right hd1) (notDom_append_right hd2) ha.2 hb.2)
  | .superCall h1 hs1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    exact RenE.superCall (RenE.vsub h1 env hc.1.1 (notDom_append_left hd1) (notDom_append_left hd2) ha.1 hb.1)
      (RenEs.vsub hs1 env hc.2 (notDom_append_right hd1) (notDom_append_right hd2) ha.2 hb.2)
  | .field h1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => RenE.field (RenE.vsub h1 env hc hd1 hd2 ha hb)
  | .new hs1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    exact RenE.new (RenEs.vsub hs1 env hc.2 hd1 hd2 ha hb)
  | .newLocal hs1 hm1, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    exact RenE.newLocal (RenEs.vsub hs1 env hc.1.2 (notDom_append_left hd1) (notDom_append_left hd2) ha.1 hb.1)
      (RenMs.vsub hm1 env.filt hc.2 (notDom_filter (notDom_append_right hd1))
        (notDom_filter (notDom_append_right hd2)) ha.2 hb.2 filter_this_no filter_this_no)
  | .ifInst h01 h11 h21, rvo, n1, n2, S, T, env, hc, hd1, hd2, ha, hb => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ha hb
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

mutual
theorem GTy.ftv_ty : forall (G : GTy), G.ty.ftv = []
  | .cls C Gs => by simp only [GTy.ty, Ty.ftv]; exact GTy.ftv_tys Gs
theorem GTy.ftv_tys : forall (Gs : List GTy), Ty.ftvList (GTy.tys Gs) = []
  | [] => rfl
  | G :: Gs => by simp only [GTy.tys, Ty.ftvList, GTy.ftv_ty G, GTy.ftv_tys Gs]; rfl
end

theorem GTy.ren_ty {rt : TRen} (G : GTy) : G.ty.ren rt = G.ty :=
  Ty.ren_id (fun X hX => by rw [GTy.ftv_ty] at hX; cases hX)

theorem GSubst.lookup_ty {sigma : GSubst} {X : TVarName} :
    List.lookup X sigma.ty = (List.lookup X sigma).map GTy.ty := by
  induction sigma with
  | nil => rfl
  | cons p sigma ih =>
    cases p with
    | mk a G =>
      simp only [GSubst.ty, List.map_cons]
      by_cases e : X = a
      . subst e; rw [lookup_cons_eq, lookup_cons_eq]; rfl
      . rw [lookup_cons_ne e, lookup_cons_ne e]; exact ih

abbrev NotDomT (Xs : List TVarName) (sigma : GSubst) : Prop :=
  forall X, List.Mem X Xs -> Not (List.Mem X (sigma.map Prod.fst))

theorem lookupT_none_of_notDom {sigma : GSubst} {X : TVarName} (h : Not (List.Mem X (sigma.map Prod.fst))) :
    List.lookup X sigma = none := by
  apply lookup_none
  intro p hp e
  apply h
  rw [<- e]
  exact List.mem_map_of_mem hp

structure GSEnv (rt rto : TRen) (s1 s2 : GSubst) (T : List TVarName) : Prop where
  st : forall X, List.Mem X T ->
    (exists G, List.lookup X s1 = some G /\ List.lookup (rn rt X) s2 = some G) \/
    (List.lookup X s1 = none /\ List.lookup (rn rt X) s2 = none /\ rn rt X = rn rto X)

theorem GSEnv.var {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T)
    {X : TVarName} (hX : List.Mem X T) :
    ((Ty.var X).ren rt).subst s2.ty = ((Ty.var X).subst s1.ty).ren rto := by
  rcases env.st X hX with h | h
  . rcases h with ⟨G, hG⟩
    simp only [Ty.ren, Ty.subst, GSubst.lookup_ty, TVarName.ren_eq, hG.1, hG.2, Option.map_some,
      Option.getD_some, GTy.ren_ty]
  . simp only [Ty.ren, Ty.subst, GSubst.lookup_ty, TVarName.ren_eq, h.1, h.2.1, Option.map_none,
      Option.getD_none]
    rw [h.2.2]

mutual
theorem GSEnv.ty {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T) :
    forall {U : Ty}, (forall X, List.Mem X U.ftv -> List.Mem X T) -> (U.ren rt).subst s2.ty = (U.subst s1.ty).ren rto
  | .var X, h => env.var (h X (by simp [Ty.ftv]))
  | .cls C Us, h => by
    simp only [Ty.ren, Ty.subst]
    rw [GSEnv.tys env (fun X hX => h X (by simpa [Ty.ftv] using hX))]
theorem GSEnv.tys {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T) :
    forall {Us : List Ty}, (forall X, List.Mem X (Ty.ftvList Us) -> List.Mem X T) ->
      Ty.substList s2.ty (Ty.renList rt Us) = Ty.renList rto (Ty.substList s1.ty Us)
  | [], _ => rfl
  | U :: Us, h => by
    simp only [Ty.renList, Ty.substList]
    rw [GSEnv.ty env (fun X hX => h X (List.mem_append_left _ hX)),
      GSEnv.tys env (fun X hX => h X (List.mem_append_right _ hX))]
end

theorem GSEnv.funnels {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T) :
    forall {Fs : List Funnel}, (forall X, List.Mem X (domF Fs) -> List.Mem X T) ->
      (Fs.map (Funnel.ren rt)).map (Funnel.gsubst s2) = (Fs.map (Funnel.gsubst s1)).map (Funnel.ren rto)
  | [], _ => rfl
  | F :: Fs, h => by
    simp only [List.map_cons, List.cons.injEq]
    refine And.intro ?_ (GSEnv.funnels env (fun X hX => h X (by rw [domF_cons]; exact List.mem_append_right _ hX)))
    cases F with
    | ground G => rfl
    | funnel X =>
      have hX : List.Mem X T := h X (by simp [domF])
      rcases env.st X hX with h' | h'
      . cases h' with
        | intro G hG => simp only [Funnel.ren, Funnel.gsubst, TVarName.ren_eq, hG.1, hG.2]
      . simp only [Funnel.ren, Funnel.gsubst, TVarName.ren_eq, h'.1, h'.2.1]
        rw [h'.2.2]

theorem GSEnv.methExt {rt rto : TRen} {s1 s2 : GSubst} {T : List TVarName} (env : GSEnv rt rto s1 s2 T)
    {Xa Xb : List TVarName} (hl : Xa.length = Xb.length) (ha : NotDomT Xa s1) (hb : NotDomT Xb s2) :
    GSEnv (Xa.zip Xb ++ rt) (Xa.zip Xb ++ rto) s1 s2 (T ++ Xa) where
  st := by
    intro X hX
    by_cases hm : List.Mem X Xa
    . have hmb := rn_zip_mem (r := rt) hl hm
      exact Or.inr (And.intro (lookupT_none_of_notDom (ha X hm))
        (And.intro (lookupT_none_of_notDom (hb _ hmb)) (rn_zip_indep hl hm)))
    . rw [rn_zip_not_mem hm, rn_zip_not_mem hm]
      have hXT : List.Mem X T := by
        simp only [listMem_iff, List.mem_append] at hX hm
        rcases hX with h | h
        . exact h
        . exact absurd h hm
      exact env.st X hXT

theorem notDomT_append_left {xs ys : List TVarName} {s : GSubst} (h : NotDomT (xs ++ ys) s) : NotDomT xs s :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem notDomT_append_right {xs ys : List TVarName} {s : GSubst} (h : NotDomT (xs ++ ys) s) : NotDomT ys s :=
  fun x hx => h x (List.mem_append_right _ hx)

theorem bounds_subst_ren {r1 r2 : TRen} {s1 s2 : TSubst} : forall {Delta : Bounds} {Xs : List TVarName},
    Xs.length = Delta.length ->
    (forall b, List.Mem b Delta -> (b.T.ren r1).subst s2 = (b.T.subst s1).ren r2) ->
    Bounds.subst s2 ((Delta.zip Xs).map fun p => ({ X := p.2, T := p.1.T.ren r1 } : Bound)) =
      ((Bounds.subst s1 Delta).zip Xs).map fun p => ({ X := p.2, T := p.1.T.ren r2 } : Bound)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: Delta, X :: Xs, hl, h => by
    simp only [Bounds.subst, List.zip_cons_cons, List.map_cons, List.cons.injEq] at |-
    refine And.intro ?_ (bounds_subst_ren (by simpa using hl) (fun b' hb' => h b' (List.Mem.tail _ hb')))
    rw [h b (List.Mem.head _)]

theorem params_subst_ren {r1 r2 : TRen} {s1 s2 : TSubst} : forall {ps : List VarDecl} {xs : List VarName},
    xs.length = ps.length ->
    (forall p, List.Mem p ps -> (p.T.ren r1).subst s2 = (p.T.subst s1).ren r2) ->
    ((ps.zip xs).map fun p => ({ T := p.1.T.ren r1, x := p.2 } : VarDecl)).map (VarDecl.subst s2) =
      ((ps.map (VarDecl.subst s1)).zip xs).map fun p => ({ T := p.1.T.ren r2, x := p.2 } : VarDecl)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | p :: ps, x :: xs, hl, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, VarDecl.subst]
    refine And.intro ?_ (params_subst_ren (by simpa using hl) (fun p' hp' => h p' (List.Mem.tail _ hp')))
    rw [h p (List.Mem.head _)]

theorem dom_bounds_subst {s : TSubst} {Delta : Bounds} : dom (Bounds.subst s Delta) = dom Delta := by
  simp [dom, Bounds.subst, List.map_map, Function.comp_def]

mutual
theorem RenE.gsub {rv rt a b} : RenE rv rt a b -> forall {rto s1 s2 T S}, GSEnv rt rto s1 s2 T ->
    a.closed T S = true -> NotDomT a.tbinders s1 -> NotDomT b.tbinders s2 ->
    RenE rv rto (a.gsubst s1) (b.gsubst s2)
  | .var, _, _, _, _, _, _, _, _, _ => by simp only [Expr.gsubst]; exact RenE.var
  | .call h1 hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.gsubst]
    rw [env.tys (all_contains_iff.mp hc.1.2)]
    exact RenE.call (RenE.gsub h1 env hc.1.1 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenEs.gsub hs1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
  | .superCall h1 hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.gsubst]
    have h2 := all_contains_iff.mp hc.1.2
    rw [env.tys (fun X hX => h2 X (List.mem_append_right _ hX)),
      env.ty (fun X hX => h2 X (List.mem_append_left _ hX))]
    exact RenE.superCall (RenE.gsub h1 env hc.1.1 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenEs.gsub hs1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
  | .field h1, rto, s1, s2, T, S, env, hc, hd1, hd2 => RenE.field (RenE.gsub h1 env hc hd1 hd2)
  | .new hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.gsubst]
    rw [env.tys (all_contains_iff.mp hc.1)]
    exact RenE.new (RenEs.gsub hs1 env hc.2 hd1 hd2)
  | .newLocal hs1 hm1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.tbinders] at hd1 hd2
    simp only [Expr.gsubst]
    have h1 := all_contains_iff.mp hc.1.1
    rw [env.tys (fun X hX => h1 X (List.mem_append_right _ hX)),
      env.funnels (fun X hX => h1 X (List.mem_append_left _ hX))]
    exact RenE.newLocal (RenEs.gsub hs1 env hc.1.2 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenMs.gsub hm1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
  | .ifInst h01 h11 h21, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closed, Bool.and_eq_true] at hc
    simp only [Expr.tbinders] at hd1 hd2
    simp only [Expr.gsubst]
    rw [env.ty (all_contains_iff.mp hc.1.1.2)]
    exact RenE.ifInst
      (RenE.gsub h01 env hc.1.1.1 (notDomT_append_left (notDomT_append_left hd1))
        (notDomT_append_left (notDomT_append_left hd2)))
      (RenE.gsub h11 env hc.1.2 (notDomT_append_right (notDomT_append_left hd1))
        (notDomT_append_right (notDomT_append_left hd2)))
      (RenE.gsub h21 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
theorem RenEs.gsub {rv rt as bs} : RenEs rv rt as bs -> forall {rto s1 s2 T S}, GSEnv rt rto s1 s2 T ->
    Expr.closedList T S as = true -> NotDomT (Expr.tbindersList as) s1 -> NotDomT (Expr.tbindersList bs) s2 ->
    RenEs rv rto (Expr.gsubstList s1 as) (Expr.gsubstList s2 bs)
  | .nil, _, _, _, _, _, _, _, _, _ => RenEs.nil
  | .cons h1 hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Expr.closedList, Bool.and_eq_true] at hc
    simp only [Expr.tbindersList] at hd1 hd2
    simp only [Expr.gsubstList]
    exact RenEs.cons (RenE.gsub h1 env hc.1 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenEs.gsub hs1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
theorem RenM.gsub {rv rt Ma Mb} : RenM rv rt Ma Mb -> forall {rto s1 s2 T S}, GSEnv rt rto s1 s2 T ->
    Ma.closed T S = true -> NotDomT Ma.tbinders s1 -> NotDomT Mb.tbinders s2 ->
    RenM rv rto (Ma.gsubst s1) (Mb.gsubst s2)
  | .mk (Delta := Da) (T0 := T0) (m := m) (ps := ps) (Xs' := Xs) (xs' := xs) hL hl h1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Method.closed, Bool.and_eq_true] at hc
    simp only [Method.tbinders] at hd1 hd2
    rw [dom_renBounds hL] at hd2
    simp only [Method.gsubst]
    have hLa : (dom Da).length = Xs.length := by simp [dom, hL]
    have env' := env.methExt hLa (notDomT_append_left hd1) (notDomT_append_left hd2)
    have hbody := RenE.gsub h1 env' hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2)
    have hm := RenM.mk (rv := rv) (rt := rto) (Delta := Bounds.subst s1.ty Da) (T0 := T0.subst s1.ty) (m := m)
      (ps := ps.map (VarDecl.subst s1.ty)) (Xs' := Xs) (xs' := xs) (by simp [Bounds.subst, hL]) (by simp [hl])
      (by rw [dom_bounds_subst]; simpa [List.map_map, Function.comp_def, VarDecl.subst] using hbody)
    have hall := all_contains_iff.mp hc.1
    rw [dom_bounds_subst] at hm
    rw [env'.ty (fun X hX => hall X (by simp only [List.cons_append]; exact List.mem_append_left _ hX)),
      bounds_subst_ren hL (fun b hb => env'.ty (fun X hX => hall X (by
        simp only [List.cons_append, Ty.ftvList]
        exact List.mem_append_right _ (by rw [ftvList_append]; exact List.mem_append_left _ (ftvList_map_mem (f := Bound.T) hb hX))))),
      params_subst_ren hl (fun p hp => env'.ty (fun X hX => hall X (by
        simp only [List.cons_append, Ty.ftvList]
        exact List.mem_append_right _ (by rw [ftvList_append]; exact List.mem_append_right _ (ftvList_map_mem (f := VarDecl.T) hp hX)))))]
    exact hm
theorem RenMs.gsub {rv rt Mas Mbs} : RenMs rv rt Mas Mbs -> forall {rto s1 s2 T S}, GSEnv rt rto s1 s2 T ->
    Method.closedList T S Mas = true -> NotDomT (Method.tbindersList Mas) s1 ->
    NotDomT (Method.tbindersList Mbs) s2 ->
    RenMs rv rto (Method.gsubstList s1 Mas) (Method.gsubstList s2 Mbs)
  | .nil, _, _, _, _, _, _, _, _, _ => RenMs.nil
  | .cons h1 hs1, rto, s1, s2, T, S, env, hc, hd1, hd2 => by
    simp only [Method.closedList, Bool.and_eq_true] at hc
    simp only [Method.tbindersList] at hd1 hd2
    simp only [Method.gsubstList]
    exact RenMs.cons (RenM.gsub h1 env hc.1 (notDomT_append_left hd1) (notDomT_append_left hd2))
      (RenMs.gsub hs1 env hc.2 (notDomT_append_right hd1) (notDomT_append_right hd2))
end

end Funnelling
