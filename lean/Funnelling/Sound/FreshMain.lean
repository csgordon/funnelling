import Funnelling.Sound.FreshSubst

open Funnelling.SoundSimp

namespace Funnelling.High

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
  fun ht => h (Expr.vbinders_vsubst ht)

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
    simp only [Method.uniq] at hu
    simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ht
    simp only [Method.noShadow, Bool.and_eq_true] at hn
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
    have hgd1 : NotDomT e1.tbinders (bind (B ++ D1) (Gs ++ Gs')) := by
      intro X hX hm; rw [hdom1] at hm; exact hgs1 X hX hm
    have hgd2 : NotDomT e2.tbinders (bind (B ++ D2) (Gs ++ Gs')) := by
      intro X hX hm; rw [hdom2] at hm; exact hgs2 X hX hm
    have hrg := RenE.gsub hr genv hca hgd1 hgd2
    have venv : VSEnv ((p1.map VarDecl.x).zip (p2.map VarDecl.x) ++ []) []
        ((this :: p1.map VarDecl.x).zip (v0 :: vs)) ((this :: p2.map VarDecl.x).zip (v0 :: vs))
        (this :: [] ++ p1.map VarDecl.x) := {
      sv := fun w hw => by
        left
        have hw' : List.Mem w (this :: p1.map VarDecl.x) := by simpa using hw
        have hwd : List.Mem w (((this :: p1.map VarDecl.x).zip (v0 :: vs)).map Prod.fst) := by
          rw [hndom1]; exact hw'
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

end Funnelling.High
