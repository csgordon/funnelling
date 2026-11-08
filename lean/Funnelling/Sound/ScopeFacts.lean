import Funnelling.Sound.Occ

open Funnelling.SoundSimp

namespace Funnelling.High

def K.gvars : K -> List TVarName
  | .dec D => dom D.bounds
  | .loc _ Fs _ _ _ _ => domF Fs

structure SF (d : Decls) (k : K) (Delta0 : Bounds) : Prop where
  closedB : forall X, List.Mem X (Ty.ftvList (cod Delta0)) -> List.Mem X (dom Delta0)
  ndom : (dom Delta0).Nodup
  gv : dom Delta0 = k.gvars
  meths : forall M, List.Mem M k.Ms -> exists gamma, MethodOk d Delta0 gamma M
  ns : forall M, List.Mem M k.Ms -> exists Xs xs, Sub1 (dom Delta0) Xs /\ Method.noShadow Xs xs M = true
  sup : forall C Fs C' Ts es Ms, k = .loc C Fs C' Ts es Ms -> forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X (domF Fs)
  supK : forall C Fs C' Ts es Ms, k = .loc C Fs C' Ts es Ms -> Kind d Delta0 (.cls C' Ts)

theorem noShadowListM_all {Xs : List TVarName} {xs : List VarName} {M : Method} : forall {Ms : List Method},
    Method.noShadowList Xs xs Ms = true -> List.Mem M Ms -> Method.noShadow Xs xs M = true
  | [], _, h => by cases h
  | M' :: Ms, hn, h => by
    simp only [Method.noShadowList, Bool.and_eq_true] at hn
    cases h with
    | head => exact hn.1
    | tail _ h => exact noShadowListM_all hn.2 h

theorem methodOk_inv {d : Decls} {Delta : Bounds} {gamma : Gamma} {Delta' : Bounds} {T0 : Ty} {m : MethName}
    {ps : List VarDecl} {e : Expr} (h : MethodOk d Delta gamma (.mk Delta' T0 m ps e)) :
    KindSeq d (Delta ++ Delta') (cod Delta') /\ KindSeq d (Delta ++ Delta') (T0 :: ps.map VarDecl.T) /\
      Typing d (Delta ++ Delta') (gamma ++ ps) e T0 := by
  cases h with
  | methodOk h1 h2 h3 => exact And.intro h1 (And.intro h2 h3)

theorem sf_dec {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {D : Dec} (hD : Declared d (.dec D)) :
    SF d (.dec D) D.bounds := by
  have hc := hok D hD.dec_mem
  refine { closedB := ?_, ndom := ?_, gv := rfl, meths := ?_, ns := ?_, sup := ?_, supK := ?_ }
  . intro X hX
    rcases ftvList_mem.mp hX with ⟨T, hT⟩; exact Kind.ftv (hc.1 T hT.1) X hT.2
  . exact hwf.2.2.2.2.1 D.bounds (by
      simp only [listMem_iff, List.mem_append, List.mem_map]
      exact Or.inl (Exists.intro D (And.intro hD.dec_mem rfl)))
  . intro M hM; exact Exists.intro _ (hc.2.2.1 M hM)
  . intro M hM
    exact Exists.intro (dom D.bounds) (Exists.intro [] (And.intro (fun _ h => h)
      (noShadowListM_all (hwf.2.2.2.2.2.2.1 D hD.dec_mem) hM)))
  . intro _ _ _ _ _ _ e; cases e
  . intro _ _ _ _ _ _ e; cases e

theorem methods_mem {d : Decls} {k : K} (hk : Declared d k) {M : Method} (hM : List.Mem M k.Ms) :
    List.Mem M d.methods := by
  simp only [Decls.methods, listMem_iff, List.mem_flatMap]
  exact Exists.intro k (And.intro hk.mem hM)

theorem scopeFacts {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {T : Ty} {Delta0 : Bounds} {Ts0 : List Ty}
    (h : Scope d T Delta0 Ts0) : exists k, Declared d k /\ (exists Us, T = .cls k.name Us) /\ SF d k Delta0 := by
  induction h with
  | @dec D Ts hD => exact Exists.intro (.dec D) (And.intro hD (And.intro (Exists.intro Ts rfl) (sf_dec hwf hok hD)))
  | @loc C Delta' T0 m ps e C0 Fs C' Ts' es Ms T Delta Ts'' Ts Delta0 Ts0 h1 h2 h3 h4 h5 ih =>
    rcases ih with ⟨k', hk'⟩
    rcases h1 with ⟨k'', hk''⟩
    have hgen : k'.name = C := by
      rcases hk'.2.1 with ⟨Us, hUs⟩
      cases h3 with
      | dec hD => simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
      | loc hD => simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
    have ek := Declared.unique hwf hk''.1 hk'.1 (by rw [hk''.2.1, hgen])
    subst ek
    have sf := hk'.2.2
    have hM := hk''.2.2
    rcases sf.meths _ hM with ⟨gamma, hmo⟩
    have hmi := methodOk_inv hmo
    rcases h2 with ⟨E, hE⟩
    rw [hE] at hmi
    rcases occ_typing E hmi.2.2 with ⟨gamma', hg⟩
    rcases hg with ⟨Ta, hTa⟩
    rcases inv_local hTa rfl with ⟨w, hw⟩
    have hdecl : Declared d (.loc C0 Fs C' Ts' es Ms) :=
      Declared.loc hk''.1 hM (Exists.intro E hE)
    rcases sf.ns _ hM with ⟨Xs, hXs⟩
    rcases hXs with ⟨xs, hxs⟩
    have hns := hxs.2
    simp only [Method.noShadow, Bool.and_eq_true] at hns
    have hnd : (dom (Delta ++ Delta')).Nodup := by
      rw [dom_append]
      apply List.nodup_append.mpr
      refine And.intro sf.ndom (And.intro ?_ ?_)
      . exact hwf.2.2.2.2.1 Delta' (by
          simp only [listMem_iff, List.mem_append, List.mem_map]
          exact Or.inr (Exists.intro _ (And.intro (methods_mem hk''.1 hM) rfl)))
      . intro X hX Y hY e
        subst e
        exact not_mem_of_all_not_contains hns.1.1 hY (hxs.1 X hX)
    have eD := Pairing.unique hnd h5 hw.pair
    subst eD
    refine Exists.intro (.loc C0 Fs C' Ts' es Ms) (And.intro hdecl (And.intro (Exists.intro Ts rfl) ?_))
    refine { closedB := hw.closedB, ndom := ?_, gv := h5.dom_eq, meths := ?_, ns := ?_, sup := ?_, supK := ?_ }
    . rw [h5.dom_eq]; exact hwf.2.2.2.2.2.1 _ hdecl.mem
    . intro M' hM'; exact Exists.intro _ (hw.meths M' hM')
    . intro M' hM'
      have hn2 := hns.2
      rw [hE] at hn2
      rcases occ_noShadow E hn2 with ⟨xs', hxs'⟩
      refine Exists.intro (Xs ++ dom Delta') (Exists.intro xs' (And.intro ?_ (noShadowListM_all hxs' hM')))
      intro X hX
      have hX2 : List.Mem X (dom (Delta ++ Delta')) := by
        have := h5.sub
        simp only [dom] at hX |-
        rcases List.mem_map.mp hX with ⟨b, hb⟩; rw [<- hb.2]; exact List.mem_map_of_mem (this b hb.1)
      rw [dom_append] at hX2
      simp only [listMem_iff, List.mem_append] at hX2 |-
      rcases hX2 with h | h
      . exact Or.inl (hxs.1 X h)
      . exact Or.inr h
    . intro C1 Fs1 C1' Ts1 es1 Ms1 e X hX
      cases e
      have := Kind.ftv hw.kindS X (by simpa [Ty.ftv] using hX)
      rwa [h5.dom_eq] at this
    . intro C1 Fs1 C1' Ts1 es1 Ms1 e
      cases e
      exact hw.kindS

def K.generic : K -> Ty
  | .dec D => .cls D.C (vars (dom D.bounds))
  | .loc C Fs _ _ _ _ => .cls C (vars (domF Fs))

theorem K.generic_name (k : K) : exists Us, k.generic = .cls k.name Us := by
  cases k <;> exact Exists.intro _ rfl

theorem Declared.generic {d : Decls} {k : K} (hk : Declared d k) : Generic d k.name k.generic := by
  cases k with
  | dec D => exact Generic.dec hk
  | loc C Fs C' Ts es Ms => exact Generic.loc hk

theorem scopeExists {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {k : K} (hk : Declared d k) :
    exists Delta0 Ts0, Scope d k.generic Delta0 Ts0 := by
  induction hk with
  | @dec D hD => exact Exists.intro _ (Exists.intro _ (Scope.dec (Declared.dec hD)))
  | @loc k Delta T0 m ps e C0 Fs C' Ts es Ms hk hM hO ih =>
    rcases ih with ⟨Dk, h⟩
    rcases h with ⟨Tk, hs⟩
    rcases scopeFacts hwf hok hs with ⟨k', hk'⟩
    have hname : k'.name = k.name := by
      rcases hk'.2.1 with ⟨Us, hUs⟩
      rcases K.generic_name k with ⟨Vs, hVs⟩; rw [hVs] at hUs; simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
    have ek := Declared.unique hwf hk'.1 hk hname
    subst ek
    rcases hk'.2.2.meths _ hM with ⟨gamma, hmo⟩
    have hmi := methodOk_inv hmo
    rcases hO with ⟨E, hE⟩
    rw [hE] at hmi
    rcases occ_typing E hmi.2.2 with ⟨gamma', hg⟩
    rcases hg with ⟨Ta, hTa⟩
    rcases inv_local hTa rfl with ⟨w, hw⟩
    have hdecl : Declared d (.loc C0 Fs C' Ts es Ms) := Declared.loc hk hM (Exists.intro E hE)
    have hab := abs_funnels (Fs := Fs) (fun F hF => hwf.2.2.2.2.2.2.2.2.2.2 _ hdecl.mem F hF)
    have hp := hw.pair
    rw [hab] at hp
    exact Exists.intro _ (Exists.intro _ (Scope.loc (Exists.intro k' (And.intro hk (And.intro rfl hM)))
      (Exists.intro E hE) hk.generic hs hp))

theorem declOk' {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) : DeclOk d where
  supD := by
    intro D hD X hX
    exact Kind.ftv ((hok D hD.dec_mem).2.1 _ (List.Mem.head _)) X (by simpa [Ty.ftv] using hX)
  supL := by
    intro C Fs C' Ts es Ms hD X hX
    rcases scopeExists hwf hok hD with ⟨Dk, h⟩
    rcases h with ⟨Tk, hs⟩
    rcases scopeFacts hwf hok hs with ⟨k', hk'⟩
    have hname : k'.name = C := by
      rcases hk'.2.1 with ⟨Us, hUs⟩; simp only [K.generic, Ty.cls.injEq] at hUs; exact hUs.1.symm
    have ek := Declared.unique hwf hk'.1 hD hname
    exact hk'.2.2.sup C Fs C' Ts es Ms ek X hX
  scopeB := by
    intro T Delta0 Ts0 hs
    rcases scopeFacts hwf hok hs with ⟨k', hk'⟩; exact hk'.2.2.closedB

end Funnelling.High