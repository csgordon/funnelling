import Funnelling.Sound.RenOver

open Funnelling.SoundSimp

namespace Funnelling.High

mutual
theorem Typing.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma e T}, Typing d Delta gamma e T ->
    forall {rv rt e' Delta' gamma' Xs xs Xs' xs'}, RenE rv rt e e' -> REnv rv rt Delta Delta' gamma gamma' Xs xs xs' ->
    e.noShadow Xs xs = true -> e'.noShadow Xs' xs' = true -> NoThis e -> NoThis e' -> e.uniq -> e'.uniq ->
    Typing d Delta' gamma' e' (T.ren rt)
  | _, _, _, _, .subs h hk hs, _, _, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' =>
    Typing.subs (Typing.ren hwf hok hd h hr env hn hn' ht ht' hu hu') (Kind.renT hd env.bD hk) (Sub.renT hd env.bD hs)
  | _, _, _, _, .var hl, _, _, _, _, _, _, _, _, _, hr, env, _, _, _, _, _, _ => by
    cases hr
    exact Typing.var (env.g _ _ hl)
  | _, _, _, _, .newObject, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _, _, _ => by
    cases hr with
    | new hs => cases hs; exact Typing.newObject
  | _, _, _, _, .declField h1 h2 h3 h4, _, _, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | field hr1 =>
      have ih := Typing.ren hwf hok hd h1 hr1 env hn hn' ht ht' hu hu'
      rw [ren_bind h4 (field_closed hok h2 h3)]
      exact Typing.declField ih h2 h3 (by rw [renList_length, h4])
  | _, _, _, _, .call (Delta0 := Delta0) (Delta1 := Delta1) (Ts2 := Ts2) (Ts1 := Ts1) h1 h2 h3 h4 h5 h6 h7 h8 h9, _, rt, _, _, _, _, _, _, _,
      hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | call hr1 hr2 =>
      simp only [Expr.noShadow, Bool.and_eq_true] at hn hn'
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht ht'
      have hcl := methodIn_closed hwf hok h2 h3
      have ih1 := Typing.ren hwf hok hd h1 hr1 env hn.1 hn'.1 ht.1 ht'.1 hu.1 hu'.1
      have ih2 := TypingSeq.ren hwf hok hd h9 hr2 env hn.2 hn'.2 ht.2 ht'.2 hu.2 hu'.2
      have hlen : (Ts2 ++ Ts1).length = (Delta0 ++ Delta1).length := by simp [h4, h5]
      have e6 := congrArg (Ty.renList rt) h6
      rw [renList_bind hlen hcl.1, renList_append] at e6
      refine Typing.call ih1 (Scope.renT h2) h3 (by rw [renList_length, h4]) (by rw [renList_length, h5]) e6
        (KindSeq.renT hd env.bD h7) ?_ ih2
      have := SubSeq.renT hd env.bD h8
      rwa [renList_bind hlen hcl.2, renList_append] at this
  | _, _, _, _, .callLbRuntime (D0 := D0) (Ts0 := Ts0) (Delta1 := Delta1) (Ts1 := Ts1) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11,
      _, rt, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | superCall hr1 hr2 =>
      have hcl := methodIn_closed hwf hok (Scope.dec (Ts := Ts0) h2) h3
      have ih := TypingSeq.ren hwf hok hd h11 (RenEs.cons hr1 hr2) env
        (by simpa [Expr.noShadowList, Expr.noShadow] using hn) (by simpa [Expr.noShadowList, Expr.noShadow] using hn')
        (by simpa [NoThis, Expr.vbindersList, Expr.vbinders] using ht)
        (by simpa [NoThis, Expr.vbindersList, Expr.vbinders] using ht')
        (by simpa [Expr.uniqList, Expr.uniq] using hu) (by simpa [Expr.uniqList, Expr.uniq] using hu')
      have hlen : (Ts0 ++ Ts1).length = (D0.bounds ++ Delta1).length := by simp [h4, h5]
      have e6 := congrArg (Ty.renList rt) h6
      rw [renList_bind hlen hcl.1, renList_append] at e6
      have hs1 := Sub.renT hd env.bD h1
      have hk8 := Kind.renT hd env.bD h8
      simp only [Ty.ren] at hs1 hk8 |-
      refine Typing.callLbRuntime hs1 h2 h3 (by rw [renList_length, h4]) (by rw [renList_length, h5]) e6 h7 hk8
        (KindSeq.renT hd env.bD h9) ?_ ih
      have := SubSeq.renT hd env.bD h10
      rwa [renList_bind hlen hcl.2, renList_append] at this
  | _, _, _, _, .newTop (D := D) h1 h2 h3 h4 h5, _, _, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | new hr1 =>
      rcases RenEs.split hr1 with ⟨a, h⟩
      rcases h with ⟨b, h⟩
      have e := h.1
      subst e
      simp only [Expr.noShadow, noShadowList_append, Bool.and_eq_true] at hn hn'
      simp only [NoThis, Expr.vbinders, vbindersList_append, listMem_iff, List.mem_append, not_or] at ht ht'
      simp only [Expr.uniq, uniqList_append] at hu hu'
      have ih1 := TypingSeq.ren hwf hok hd h4 h.2.1 env hn.1 hn'.1 ht.1 ht'.1 hu.1 hu'.1
      have ih2 := Typing.ren hwf hok hd h5 (RenE.new h.2.2) env (by simpa [Expr.noShadow] using hn.2)
        (by simpa [Expr.noShadow] using hn'.2) (by simpa [NoThis, Expr.vbinders] using ht.2)
        (by simpa [NoThis, Expr.vbinders] using ht'.2) (by simpa [Expr.uniq] using hu.2)
        (by simpa [Expr.uniq] using hu'.2)
      rw [renList_bind h3 (slots_closed hok h1)] at ih1
      rw [renList_bind h3 (hd.supD D h1)] at ih2
      have hk2 := Kind.renT hd env.bD h2
      simp only [Ty.ren] at hk2 |-
      exact Typing.newTop h1 hk2 (by rw [renList_length, h3]) ih1 ih2
  | _, _, _, _, .newLocal (C := C) (Fs := Fs) (C0 := C0) (Ts := Ts) (Ms := Ms) (Delta' := Dp) h1 h2 h3 h4 h5 h6 h7 h8,
      rv, rt, _, Delta', gamma', Xs, xs, Xs', xs', hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | newLocal hr1 hr2 =>
      simp only [Expr.noShadow, Bool.and_eq_true] at hn hn'
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ht ht'
      have hbq : BRen rt Dp (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) :=
        fun b hb => List.mem_map_of_mem (f := fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) hb
      have hDX : forall X, List.Mem X (dom Dp) -> List.Mem X Xs := fun X hX => env.dX X (dom_sub1 h2.sub X hX)
      have hFs : forall X, List.Mem X (Ty.ftvList (abs Fs)) -> List.Mem X Xs := fun X hX => hDX X (Kind.ftv h4 X hX)
      have hTs : forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X Xs := fun X hX => hDX X (Kind.ftv h5 X hX)
      have hdisM : forall M, List.Mem M Ms -> forall X, List.Mem X Xs -> Not (List.Mem X (dom M.bounds)) :=
        fun M hM X hX hm => Method.noShadow_dom (noShadowListM_mem hM hn.2) X hm hX
      have huM : forall M, List.Mem M Ms -> M.uniq := fun M hM => uniqList_mem hM hu.2
      have ih6 := Typing.ren hwf hok hd h6 (RenE.new hr1) env (by simpa [Expr.noShadow] using hn.1)
        (by simpa [Expr.noShadow] using hn'.1) (by simpa [NoThis, Expr.vbinders] using ht.1)
        (by simpa [NoThis, Expr.vbinders] using ht'.1) (by simpa [Expr.uniq] using hu.1)
        (by simpa [Expr.uniq] using hu'.1)
      have hp := Pairing.renT env.bD h2
      rw [<- abs_ren] at hp
      have hk4 := Kind.renT hd hbq h4
      have hk5 := Kind.renT hd hbq h5
      simp only [Ty.ren] at hk4 hk5 |-
      rw [<- abs_ren] at hk4 |-
      refine Typing.newLocal (Consistent.ren hwf hok hd h1 hr2 (fun M hM X hX => hdisM M hM X (hFs X hX)) huM) hp
        ?_ hk4 hk5 ih6 ?_ (OverrideOk.ren hwf hok hd h8 hr2 (fun M hM X hX => hdisM M hM X (hTs X hX)) huM)
      . intro X hX
        have ec : cod (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) = Ty.renList rt (cod Dp) := by
          simp [cod, Ty.renList_eq_map]
        have ed : dom (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) = (dom Dp).map (rn rt) := by
          simp [dom]
        rw [ec, Ty.ftvList_ren] at hX
        rw [ed]
        rcases List.mem_map.mp hX with ⟨Y, hY⟩; rw [<- hY.2]; exact List.mem_map_of_mem (h3 Y hY.1)
      . intro M' hM'
        rcases RenMs.mem_inv hr2 hM' with ⟨M, hM⟩
        exact MethodOk.ren hwf hok hd (h7 M hM.1) hM.2 (env.inner h2 hFs C) (noShadowListM_mem hM.1 hn.2)
          (noShadowListM_mem hM' hn'.2) (fun h => ht.2 (vbindersListM_mem hM.1 h))
          (fun h => ht'.2 (vbindersListM_mem hM' h)) (huM M hM.1) (uniqList_mem hM' hu'.2)
  | _, _, _, _, .ifInstanceof (x := x) h0 hk hc h1 h2, _, _, _, _, _, _, xs, _, xs', hr, env, hn, hn', ht, ht', hu,
      hu' => by
    cases hr with
    | @ifInst _ _ _ _ _ _ y _ _ _ _ hr0 hr1 hr2 =>
      simp only [Expr.noShadow, Bool.and_eq_true, Bool.not_eq_true'] at hn hn'
      simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ht ht'
      have hxs : Not (List.Mem x xs) := by have := hn.1.1.2; simp at this; exact this
      have hys : Not (List.Mem y xs') := by have := hn'.1.1.2; simp at this; exact this
      have env1 := env.ext hxs hys (fun X hX => env.dX X (Kind.ftv hk X hX)) (fun e => ht.1.1.1 e.symm)
        (fun e => ht'.1.1.1 e.symm)
      exact Typing.ifInstanceof (Typing.ren hwf hok hd h0 hr0 env hn.1.1.1 hn'.1.1.1 ht.1.1.2 ht'.1.1.2 hu.1 hu'.1)
        (Kind.renT hd env.bD hk) (Cast.renT hd env.bD hc)
        (Typing.ren hwf hok hd h1 hr1 env1 hn.1.2 hn'.1.2 ht.1.2 ht'.1.2 hu.2.1 hu'.2.1)
        (Typing.ren hwf hok hd h2 hr2 env hn.2 hn'.2 ht.2 ht'.2 hu.2.2 hu'.2.2)
theorem TypingSeq.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma es Ts}, TypingSeq d Delta gamma es Ts ->
    forall {rv rt es' Delta' gamma' Xs xs Xs' xs'}, RenEs rv rt es es' ->
    REnv rv rt Delta Delta' gamma gamma' Xs xs xs' ->
    Expr.noShadowList Xs xs es = true -> Expr.noShadowList Xs' xs' es' = true ->
    Not (List.Mem this (Expr.vbindersList es)) -> Not (List.Mem this (Expr.vbindersList es')) ->
    Expr.uniqList es -> Expr.uniqList es' -> TypingSeq d Delta' gamma' es' (Ty.renList rt Ts)
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _, _, _ => by
    cases hr; exact TypingSeq.nil
  | _, _, _, _, .cons h hs, _, _, _, _, _, _, _, _, _, hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | cons hr1 hr2 =>
      simp only [Expr.noShadowList, Bool.and_eq_true] at hn hn'
      simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ht ht'
      exact TypingSeq.cons (Typing.ren hwf hok hd h hr1 env hn.1 hn'.1 ht.1 ht'.1 hu.1 hu'.1)
        (TypingSeq.ren hwf hok hd hs hr2 env hn.2 hn'.2 ht.2 ht'.2 hu.2 hu'.2)
theorem MethodOk.ren {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) (hd : DeclOk d) :
    forall {Delta gamma M}, MethodOk d Delta gamma M ->
    forall {rv rt M' Delta' gamma' Xs xs Xs' xs'}, RenM rv rt M M' ->
    REnv rv rt Delta Delta' gamma gamma' Xs (this :: xs) (this :: xs') ->
    M.noShadow Xs xs = true -> M'.noShadow Xs' xs' = true -> NoThisM M -> NoThisM M' -> M.uniq -> M'.uniq ->
    MethodOk d Delta' gamma' M'
  | Delta, _, _, .methodOk (Delta' := Dm) (T0 := T0) (ps := ps) h1 h2 h3, rv, rt, _, Delta', gamma', Xs, xs, Xs',
      xs', hr, env, hn, hn', ht, ht', hu, hu' => by
    cases hr with
    | @mk _ _ _ _ _ _ _ e2 Ys ys hL hl hb =>
      simp only [Method.noShadow, Bool.and_eq_true] at hn hn'
      simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ht ht'
      simp only [Method.uniq] at hu hu'
      rw [dom_renBounds hL, names_renParams hl] at hn' hu'
      rw [names_renParams hl] at ht'
      have hc1 : forall b, List.Mem b Dm -> forall X, List.Mem X b.T.ftv -> List.Mem X (Xs ++ dom Dm) := by
        intro b hb X hX
        have := Kind.ftv (h1 b.T (List.mem_map_of_mem (f := Bound.T) hb)) X hX
        rw [dom_append] at this
        simp only [listMem_iff, List.mem_append] at this |-
        rcases this with h | h
        . exact Or.inl (env.dX X h)
        . exact Or.inr h
      have hc2 : forall p, List.Mem p ps -> forall X, List.Mem X p.T.ftv -> List.Mem X (Xs ++ dom Dm) := by
        intro p hp X hX
        have := Kind.ftv (h2 p.T (List.Mem.tail _ (List.mem_map_of_mem (f := VarDecl.T) hp))) X hX
        rw [dom_append] at this
        simp only [listMem_iff, List.mem_append] at this |-
        rcases this with h | h
        . exact Or.inl (env.dX X h)
        . exact Or.inr h
      have env2 := env.meth hL hl (fun X hX => not_mem_of_all_not_contains hn.1.1 hX)
        hn.1.2 ht.1
        (fun x hx => not_mem_of_all_not_contains hn'.1.2 hx) ht'.1 hu.1 hu.2.1 hu'.2.1 hc1 hc2
      have ih := Typing.ren hwf hok hd h3 hb env2 hn.2 hn'.2 ht.2 ht'.2 hu.2.2 hu'.2.2
      refine MethodOk.methodOk ?_ ?_ ih
      . have := KindSeq.renT hd env2.bD h1
        rw [show cod ((Dm.zip Ys).map fun p => ({ X := p.2, T := p.1.T.ren ((dom Dm).zip Ys ++ rt) } : Bound)) =
          Ty.renList ((dom Dm).zip Ys ++ rt) (cod Dm) by
            simp only [cod, List.map_map, Ty.renList_eq_map]; exact map_zip_fst (f := fun b => b.T.ren ((dom Dm).zip Ys ++ rt)) hL]
        exact this
      . have := KindSeq.renT hd env2.bD h2
        rw [show ((ps.zip ys).map fun p => ({ T := p.1.T.ren ((dom Dm).zip Ys ++ rt), x := p.2 } : VarDecl)).map
          VarDecl.T = Ty.renList ((dom Dm).zip Ys ++ rt) (ps.map VarDecl.T) by
            simp only [List.map_map, Ty.renList_eq_map]; exact map_zip_fst (f := fun p => p.T.ren ((dom Dm).zip Ys ++ rt)) hl]
        simpa only [Ty.renList] using this
end

end Funnelling.High
