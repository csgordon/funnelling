import Funnelling.Sound.WellFormedness

open Funnelling.SoundSimp

namespace Funnelling

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

theorem CompEnv.base (B : List TVarName) : CompEnv [] [] [] [] [] [] [] [] B B where
  sv := fun _ h => by cases h
  st := fun X hX => And.intro hX rfl
  k1 := fun _ h => by cases h
  k2 := fun _ h => by cases h
  k3 := fun _ h => by cases h

theorem CompEnv.single (x : VarName) : CompEnv [] [] [] [] [] [] [x] [x] [] [] where
  sv := fun w hw _ => And.intro hw rfl
  st := fun _ h => by cases h
  k1 := fun _ h => by cases h
  k2 := fun _ h => by cases h
  k3 := fun _ h => by cases h

theorem notDom_single {e : Expr} {x : VarName} {v : Value} (h : VSubstDefined [x] e) :
    NotDom e.vbinders [(x, v)] := by
  intro y hy hm
  exact h y hy (by simpa using hm)

theorem noThis_of_vsubst {e : Expr} {n : VSubst} (h : NoThis (e.vsubst n)) : NoThis e :=
  fun ht => h ((Expr.vsubst_back _ _).1 _ ht)

theorem renE_if {e1 e1' e1'' : Expr} {x : VarName} {v : Value} (h1 : RenE [] [] e1' e1)
    (h2 : RenE [] [] e1 e1'') (hd1 : VSubstDefined [x] e1') (hd2 : VSubstDefined [x] e1'')
    (hw1 : WFExpr (e1'.vsubst [(x, v)])) (hw2 : WFExpr (e1''.vsubst [(x, v)]))
    (hn : e1.noShadow [] [x] = true) (hu : e1.uniq) (ht : NoThis e1)
    (hv : v.expr.closed [] [] = true) :
    RenE [] [] (e1'.vsubst [(x, v)]) (e1''.vsubst [(x, v)]) := by
  have hc1 : e1'.closed [] [x] = true := by
    have := Expr.closed_of_vsubst hw1.2.2.2.2.2.2
    simpa using this
  have nt1 := noThis_of_vsubst hw1.noThis
  have nt2 := noThis_of_vsubst hw2.noThis
  have hr := RenE.comp h1 h2 (CompEnv.single x) hc1 hn nt1 ht hu
  have env : VSEnv [] [] [(x, v)] [(x, v)] [x] := {
    sv := fun w hw => by
      have e : w = x := by simpa using hw
      subst e
      exact Or.inl (Exists.intro v (And.intro lookup_cons_eq lookup_cons_eq))
    k := fun _ h => by cases h
    ko := fun _ h => by cases h
    c1 := fun p hp => by
      have e : p = (x, v) := by simpa using hp
      subst e; exact hv }
  exact RenE.vsub hr env hc1 (notDom_single hd1) (notDom_single hd2) nt1 nt2

theorem fresh_if {e1 e1' e1'' : Expr} {x : VarName} {v : Value} (h1 : Fresh e1 e1')
    (h2 : Fresh e1 e1'') (hd1 : VSubstDefined [x] e1') (hd2 : VSubstDefined [x] e1'')
    (hw1 : WFExpr (e1'.vsubst [(x, v)])) (hw2 : WFExpr (e1''.vsubst [(x, v)]))
    (hn : e1.noShadow [] [x] = true) (hu : e1.uniq) (ht : NoThis e1)
    (hv : v.expr.closed [] [] = true) :
    Fresh (e1'.vsubst [(x, v)]) (e1''.vsubst [(x, v)]) :=
  And.intro (renE_if h1.2 h2.1 hd1 hd2 hw1 hw2 hn hu ht hv) (renE_if h2.2 h1.1 hd2 hd1 hw2 hw1 hn hu ht hv)

theorem dom_append {D1 D2 : Bounds} : dom (D1 ++ D2) = dom D1 ++ dom D2 := by simp [dom]

theorem bind_fst {A : Type} {D : Bounds} {as : List A} (h : as.length = D.length) :
    (bind D as).map Prod.fst = dom D := by
  simp only [bind]; exact zip_map_fst (by simp [dom, h])

theorem renE_meth {M : Method} {B : Bounds} {Gs Gs' : List GTy} {v0 : Value} {vs : List Value}
    {D1 D2 : Bounds} {T1 T2 : Ty} {m1 m2 : MethName} {p1 p2 : List VarDecl} {e1 e2 : Expr}
    (h1 : RenM [] [] (.mk D1 T1 m1 p1 e1) M) (h2 : RenM [] [] M (.mk D2 T2 m2 p2 e2))
    (hu : M.uniq) (ht : NoThisM M) (hn : Method.noShadow (dom B) [] M = true)
    (hG : Gs.length = B.length) (hG1 : Gs'.length = D1.length) (hG2 : Gs'.length = D2.length)
    (hl1 : p1.length = vs.length) (hl2 : p2.length = vs.length)
    (hN1 : (dom B ++ dom D1).Nodup) (hN2 : (dom B ++ dom D2).Nodup)
    (hn1 : (this :: p1.map VarDecl.x).Nodup) (hn2 : (this :: p2.map VarDecl.x).Nodup)
    (hgs1 : GSubstDefined (dom B ++ dom D1) e1) (hgs2 : GSubstDefined (dom B ++ dom D2) e2)
    (hvs1 : VSubstDefined (this :: p1.map VarDecl.x) e1) (hvs2 : VSubstDefined (this :: p2.map VarDecl.x) e2)
    (hc1 : ((e1.gsubst (bind (B ++ D1) (Gs ++ Gs'))).vsubst
      ((this :: p1.map VarDecl.x).zip (v0 :: vs))).closed [] [] = true)
    (hv : forall v, List.Mem v (v0 :: vs) -> v.expr.closed [] [] = true) :
    RenE [] [] ((e1.gsubst (bind (B ++ D1) (Gs ++ Gs'))).vsubst ((this :: p1.map VarDecl.x).zip (v0 :: vs)))
      ((e2.gsubst (bind (B ++ D2) (Gs ++ Gs'))).vsubst ((this :: p2.map VarDecl.x).zip (v0 :: vs))) := by
  cases M with
  | mk Da Ta m ps e =>
    have b1 := RenM.body h1
    have b2 := RenM.body h2
    simp only [Method.uniq, NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or, Method.noShadow,
      Bool.and_eq_true] at hu ht hn
    have hlen1 : (p1.map VarDecl.x).length = (ps.map VarDecl.x).length := by simp [b1.2.2.1]
    have hlen2 : (ps.map VarDecl.x).length = (p2.map VarDecl.x).length := by simp [b2.2.2.1]
    have hLen1 : (dom D1).length = (dom Da).length := by simp [dom, b1.2.1]
    have hLen2 : (dom Da).length = (dom D2).length := by simp [dom, b2.2.1]
    have htp1 : Not (List.Mem this (p1.map VarDecl.x)) := (List.nodup_cons.mp hn1).1
    have htp2 : Not (List.Mem this (p2.map VarDecl.x)) := (List.nodup_cons.mp hn2).1
    have env := (CompEnv.base (dom B)).methExt hlen1 hlen2 hu.2.1 hLen1 hLen2 hu.1 htp1 ht.1
      (by simp) hn.1.1
    have hdom1 : (bind (B ++ D1) (Gs ++ Gs')).map Prod.fst = dom B ++ dom D1 := by
      rw [bind_fst (by simp [hG, hG1]), dom_append]
    have hdom2 : (bind (B ++ D2) (Gs ++ Gs')).map Prod.fst = dom B ++ dom D2 := by
      rw [bind_fst (by simp [hG, hG2]), dom_append]
    have hndom1 : ((this :: p1.map VarDecl.x).zip (v0 :: vs)).map Prod.fst = this :: p1.map VarDecl.x :=
      zip_map_fst (by simp [hl1])
    have hcv := Expr.closed_of_vsubst hc1
    rw [hndom1] at hcv
    have hcg := Expr.closed_of_gsubst hcv
    rw [hdom1] at hcg
    have hca : e1.closed (dom B ++ dom D1) (this :: [] ++ p1.map VarDecl.x) = true :=
      Expr.closed_mono hcg (fun X hX => by simpa using hX) (fun x hx => by simpa using hx)
    have nt1 : NoThis e1 := fun h => hvs1 this h (List.Mem.head _)
    have nt2 : NoThis e2 := fun h => hvs2 this h (List.Mem.head _)
    have hr := RenE.comp b1.1 b2.1 env hca hn.2 nt1 ht.2 hu.2.2
    have genv : GSEnv ((dom D1).zip (dom D2) ++ []) [] (bind (B ++ D1) (Gs ++ Gs')) (bind (B ++ D2) (Gs ++ Gs'))
        (dom B ++ dom D1) := {
      st := fun X hX => by
        left
        have hXd : List.Mem X ((bind (B ++ D1) (Gs ++ Gs')).map Prod.fst) := by rw [hdom1]; exact hX
        rcases lookup_isSome hXd with ⟨G, hGl⟩
        refine Exists.intro G (And.intro hGl ?_)
        rw [<- hGl]
        simp only [bind, dom_append]
        refine (lookup_zip_ren ?_ hN2 ?_ hX).symm
        . simp [dom, b2.2.1, b1.2.1]
        . intro p hp
          rw [List.zip_append (by simp)] at hp
          simp only [listMem_iff, List.mem_append] at hp
          rcases hp with hp | hp
          . have e := zip_self_eq hp
            have hp1 : List.Mem p.1 (dom B) := by
              have := (List.of_mem_zip hp).1
              exact this
            have hnot : Not (List.Mem p.1 (dom D1)) := fun h => nodup_append_disj hN1 hp1 h
            rw [rn_zip_not_mem hnot, rn_nil, e]
          . exact rn_zip_pair (nodup_append_right hN1) hp }
    have hgd1 : NotDom e1.tbinders (bind (B ++ D1) (Gs ++ Gs')) := by
      intro X hX hm; rw [hdom1] at hm; exact hgs1 X hX hm
    have hgd2 : NotDom e2.tbinders (bind (B ++ D2) (Gs ++ Gs')) := by
      intro X hX hm; rw [hdom2] at hm; exact hgs2 X hX hm
    have hrg := RenE.gsub hr genv hca hgd1 hgd2
    have venv : VSEnv ((p1.map VarDecl.x).zip (p2.map VarDecl.x) ++ []) []
        ((this :: p1.map VarDecl.x).zip (v0 :: vs)) ((this :: p2.map VarDecl.x).zip (v0 :: vs))
        (this :: [] ++ p1.map VarDecl.x) := {
      sv := fun w hw => by
        left
        have hw' : List.Mem w (this :: p1.map VarDecl.x) := by simpa using hw
        have hwd : List.Mem w (((this :: p1.map VarDecl.x).zip (v0 :: vs)).map Prod.fst) := by rw [hndom1]; exact hw'
        rcases lookup_isSome hwd with ⟨v, hvl⟩
        refine Exists.intro v (And.intro hvl ?_)
        rw [<- hvl]
        refine (lookup_zip_ren ?_ hn2 ?_ hw').symm
        . simp [hl1, hl2]
        . intro p hp
          simp only [List.zip_cons_cons] at hp
          cases hp with
          | head => rw [rn_zip_not_mem htp1]; rfl
          | tail _ hp => exact rn_zip_pair (List.nodup_cons.mp hn1).2 hp
      k := fun p hp => by
        simp only [List.append_nil] at hp
        have h12 := List.of_mem_zip hp
        exact And.intro (fun e => htp1 (e ▸ h12.1)) (fun e => htp2 (e ▸ h12.2))
      ko := fun _ h => by cases h
      c1 := fun p hp => hv p.2 (List.of_mem_zip hp).2 }
    have hvd1 : NotDom (e1.gsubst (bind (B ++ D1) (Gs ++ Gs'))).vbinders ((this :: p1.map VarDecl.x).zip (v0 :: vs)) := by
      intro x hx hm; rw [Expr.vbinders_gsubst] at hx; rw [hndom1] at hm; exact hvs1 x hx hm
    have hvd2 : NotDom (e2.gsubst (bind (B ++ D2) (Gs ++ Gs'))).vbinders ((this :: p2.map VarDecl.x).zip (v0 :: vs)) := by
      intro x hx hm; rw [Expr.vbinders_gsubst] at hx; rw [zip_map_fst (by simp [hl2])] at hm; exact hvs2 x hx hm
    have nt1' : NoThis (e1.gsubst (bind (B ++ D1) (Gs ++ Gs'))) := by
      intro h; rw [Expr.vbinders_gsubst] at h; exact nt1 h
    have nt2' : NoThis (e2.gsubst (bind (B ++ D2) (Gs ++ Gs'))) := by
      intro h; rw [Expr.vbinders_gsubst] at h; exact nt2 h
    exact RenE.vsub hrg venv (Expr.closed_mono hcv (fun _ h => h) (fun x hx => by simpa using hx))
      hvd1 hvd2 nt1' nt2'

theorem nodup_map_inj {A B : Type} {f : A -> B} : forall {l : List A}, (l.map f).Nodup ->
    forall {x y : A}, List.Mem x l -> List.Mem y l -> f x = f y -> x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, hn, x, y, hx, hy, he => by
    simp only [List.map_cons, List.nodup_cons] at hn
    cases hx with
    | head =>
      cases hy with
      | head => rfl
      | tail _ hy => exact absurd (he ▸ List.mem_map_of_mem hy) hn.1
    | tail _ hx =>
      cases hy with
      | head => exact absurd (he.symm ▸ List.mem_map_of_mem hx) hn.1
      | tail _ hy => exact nodup_map_inj hn.2 hx hy he

theorem Declared.dec_mem {d : Decls} {D : Dec} (h : Declared d (.dec D)) : List.Mem D d := by
  cases h with
  | dec h => exact h

theorem dec_unique {d : Decls} (hwf : WFDecls d) {D1 D2 : Dec} (he : D1.C = D2.C) (h1 : Declared d (.dec D1))
    (h2 : Declared d (.dec D2)) : D1 = D2 := by
  have := nodup_map_inj hwf.1 (classes_mem_dec h1.dec_mem) (classes_mem_dec h2.dec_mem) he
  cases this; rfl

theorem find_unique {A : Type} {p : A -> Bool} {x : A} : forall {l : List A},
    (forall y, List.Mem y l -> p y = true -> y = x) -> List.Mem x l -> p x = true -> l.find? p = some x
  | [], _, hx, _ => by cases hx
  | a :: l, h, hx, hp => by
    by_cases ha : p a = true
    . rw [List.find?_cons_of_pos ha, h a (List.Mem.head _) ha]
    . rw [List.find?_cons_of_neg ha]
      cases hx with
      | head => exact absurd hp ha
      | tail _ hx => exact find_unique (fun y hy hpy => h y (List.Mem.tail _ hy) hpy) hx hp

theorem findDec_self {d : Decls} (hwf : WFDecls d) {D : Dec} (h : List.Mem D d) : findDec d D.C = some D := by
  apply find_unique
  . intro y hy hp
    exact dec_unique hwf (by simpa using hp) (.dec hy) (.dec h)
  . exact h
  . simp

theorem fields_nodup {d : Decls} (hwf : WFDecls d) {D : Dec} (h : List.Mem D d) : (D.Ss.map Slot.f).Nodup := by
  have h2 := hwf.2.1 D h
  simp only [superChain, findDec_self hwf h] at h2
  by_cases ho : (D.C == Object) = true
  . simp_all
  . simp only [ho] at h2
    exact nodup_append_left h2

theorem zip_unique {A B : Type} : forall {xs : List A} {ys : List B} {x : A} {y y' : B}, xs.Nodup ->
    List.Mem (x, y) (xs.zip ys) -> List.Mem (x, y') (xs.zip ys) -> y = y'
  | [], _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, _, h, _ => by cases h
  | a :: xs, b :: ys, x, y, y', hn, h1, h2 => by
    cases h1 with
    | head =>
      cases h2 with
      | head => rfl
      | tail _ h2 => exact absurd (List.of_mem_zip h2).1 (List.nodup_cons.mp hn).1
    | tail _ h1 =>
      cases h2 with
      | head => exact absurd (List.of_mem_zip h1).1 (List.nodup_cons.mp hn).1
      | tail _ h2 => exact zip_unique (List.nodup_cons.mp hn).2 h1 h2

theorem zip_mem_fst {A B : Type} {xs : List A} {ys : List B} {x : A} {y : B} (h : List.Mem (x, y) (xs.zip ys)) :
    List.Mem x xs := (List.of_mem_zip h).1

theorem FreshM.name {M : Method} {D : Bounds} {T : Ty} {m : MethName} {ps : List VarDecl} {e : Expr}
    (h : FreshM M (.mk D T m ps e)) : M.name = m := by
  cases M with
  | mk D' T' m' ps' e' => exact (RenM.body h.1).2.2.2

theorem FreshM.mem_names {M : Method} {Ms : List Method} {D T m ps e} (hM : List.Mem M Ms)
    (h : FreshM M (.mk D T m ps e)) : List.Mem m (Ms.map Method.name) :=
  FreshM.name h ▸ List.mem_map_of_mem hM

theorem closed_cons_vals {v0 : Value} {vs : List Value} (h0 : v0.expr.closed [] [] = true)
    (hs : Expr.closedList [] [] (Value.exprs vs) = true) :
    forall v, List.Mem v (v0 :: vs) -> v.expr.closed [] [] = true := by
  intro v hv
  cases hv with
  | head => exact h0
  | tail _ hv => exact Expr.closedList_mem (Value.mem_exprs hv) hs

theorem det_base {d : Decls} (hwf : WFDecls d) {a a' b1 b2 : Expr} (ha : WFExpr a) (hw1 : WFExpr b1)
    (hw2 : WFExpr b2) (h1 : BaseStep d a b1) (h2 : BaseStep d a' b2) (he : a = a') : Fresh b1 b2 := by
  revert he
  cases h1 <;> cases h2 <;> simp only [Function.Injective.eq_iff (f := Value.expr) (fun _ _ => Value.expr_inj),
    Function.Injective.eq_iff (f := GTy.tys) (fun _ _ => GTy.tys_inj), Function.Injective.eq_iff (f := Value.exprs)
    (fun _ _ => Value.exprs_inj), Expr.field.injEq, Expr.ifInst.injEq, Expr.call.injEq, Expr.superCall.injEq,
    Ty.cls.injEq, Value.new.injEq, Value.newLocal.injEq, reduceCtorEq, false_and, false_implies, and_imp] <;>
    intros <;> subst_vars <;> injections <;> subst_vars <;>
    (try obtain rfl := dec_unique hwf (by assumption : Dec.C _ = Dec.C _) (by assumption) (by assumption)) <;>
    (try obtain ⟨rfl, rfl⟩ := List.append_inj (by assumption : _ ++ _ = _ ++ _) (by omega)) <;>
    first
    | exact Fresh.refl _
    | exact absurd (zip_mem_fst (by assumption : List.Mem (_, _) _)) (by assumption)
    | exact absurd (FreshM.mem_names (by assumption) (by assumption)) (by assumption)
    | exact ((by assumption : Not (exists Ts', Sub d [] _ (.cls _ Ts'))) ⟨_, (by assumption)⟩).elim
    | skip
  case simpleFieldFound.simpleFieldFound =>
    rename_i hm _ _ _ hm' _
    exact zip_unique (fields_nodup hwf (by assumption : Declared d _).dec_mem) hm hm' ▸ Fresh.refl _
  case ifThen.ifThen =>
    rename_i hf2 hd2 hd hf _
    have hn := ha.2.2.2.2.1
    have hu := ha.uniq
    have ht := ha.noThis
    have hc := ha.2.2.2.2.2.2
    simp only [Expr.noShadow, Expr.closed, Bool.and_eq_true, NoThis, Expr.vbinders, listMem_iff, List.mem_append,
      List.mem_cons, not_or] at hn ht hc
    exact fresh_if hf hf2 hd hd2 hw1 hw2 hn.1.2 hu.2.1 ht.1.2 hc.1.1.1
  case simpleFound.simpleFound =>
    rename_i hD hM hN hN' hgs hvs _ _ _ _ _ _ _ _ _ _ hF2 hG2' hN2' hp2 hvs2 hF hG hG' hp _ hM2 _ hN2 hgs2 _
    obtain rfl := nodup_map_inj (hwf.2.2.1 _ (classes_mem_dec hD.dec_mem)) hM hM2
      (by rw [FreshM.name hF, FreshM.name hF2])
    have hMf := hwf.method hD.dec_mem hM
    have hc := ha.2.2.2.2.2.2
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have hvals := closed_cons_vals hc.1.1 hc.2
    exact And.intro
      (renE_meth hF.2 hF2.1 hMf.1 hMf.2.1 hMf.2.2 hG hG' hG2' hp hp2 hN hN2 hN' hN2' hgs hgs2 hvs hvs2
        hw1.2.2.2.2.2.2 hvals)
      (renE_meth hF2.2 hF.1 hMf.1 hMf.2.1 hMf.2.2 hG hG2' hG' hp2 hp hN2 hN hN2' hN' hgs2 hgs hvs2 hvs
        hw2.2.2.2.2.2.2 hvals)
  case innerFound.innerFound =>
    rename_i hN hN' hgs hvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ hM2 hF2 hG2 hp2 hN2 hN2' hgs2 hvs2 hF hG hp hM
    obtain rfl := nodup_map_inj (ha.1 _ (List.mem_append_left _ (List.Mem.head _))) hM hM2
      (by rw [FreshM.name hF, FreshM.name hF2])
    have hc := ha.2.2.2.2.2.2
    simp only [Expr.closed, Bool.and_eq_true] at hc
    have hvals := closed_cons_vals hc.1.1 hc.2
    rcases WFExpr.local_method (WFExpr.plug (E := .callRecv .hole _ _ _) ha) hM with ⟨hMn, hMt, hMu, -⟩
    exact And.intro
      (renE_meth (B := []) (Gs := []) hF.2 hF2.1 hMu hMt hMn rfl hG hG2 hp hp2 hN hN2 hN' hN2' hgs hgs2 hvs hvs2
        hw1.2.2.2.2.2.2 hvals)
      (renE_meth (B := []) (Gs := []) hF2.2 hF.1 hMu hMt hMn rfl hG2 hG hp2 hp hN2 hN hN2' hN' hgs2 hgs hvs2 hvs
        hw2.2.2.2.2.2.2 hvals)

end Funnelling
