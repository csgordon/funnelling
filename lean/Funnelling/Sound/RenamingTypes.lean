import Funnelling.Sound.VarSubstitution

open Funnelling.SoundSimp

namespace Funnelling

abbrev tS (rt : TRen) : TSubst := rt.map fun p => (p.1, Ty.var p.2)

theorem lookup_tS {X : TVarName} : forall {rt : TRen}, (Ty.var X).subst (tS rt) = Ty.var (rn rt X)
  | [] => rfl
  | (a, b) :: rt => by
    by_cases e : X = a
    . subst e
      simp only [tS, List.map_cons, Ty.subst]
      rw [lookup_cons_eq, rn_cons_eq]
      rfl
    . have ih := @lookup_tS X rt
      simp only [tS, List.map_cons, Ty.subst]
      rw [lookup_cons_ne e, rn_cons_ne e]
      exact ih

mutual
theorem Ty.ren_subst {rt : TRen} : forall (T : Ty), T.ren rt = T.subst (tS rt)
  | .var X => by
    rw [lookup_tS]
    rfl
  | .cls C Ts => by
    simp only [Ty.ren, Ty.subst]
    rw [Ty.renList_subst Ts]
theorem Ty.renList_subst {rt : TRen} : forall (Ts : List Ty), Ty.renList rt Ts = Ty.substList (tS rt) Ts
  | [] => rfl
  | T :: Ts => by
    simp only [Ty.renList, Ty.substList]
    rw [Ty.ren_subst T, Ty.renList_subst Ts]
end

mutual
theorem Ty.ftv_ren {rt : TRen} : forall (T : Ty), (T.ren rt).ftv = T.ftv.map (rn rt)
  | .var _ => rfl
  | .cls _ Ts => Ty.ftvList_ren Ts
theorem Ty.ftvList_ren {rt : TRen} : forall (Ts : List Ty), Ty.ftvList (Ty.renList rt Ts) = (Ty.ftvList Ts).map (rn rt)
  | [] => rfl
  | T :: Ts => by
    simp only [Ty.renList, Ty.ftvList, List.map_append]
    rw [Ty.ftv_ren T, Ty.ftvList_ren Ts]
end

theorem Ty.ren_congr {r1 r2 : TRen} {T : Ty} (h : forall X, List.Mem X T.ftv -> rn r1 X = rn r2 X) :
    T.ren r1 = T.ren r2 := by
  have := Ty.ren_comp (rt1 := []) (rt2 := r1) (rt3 := r2) (T := T) (fun X hX => by rw [rn_nil]; exact h X hX)
  rwa [Ty.ren_idRen (rt := []) (fun p hp => by cases hp)] at this

theorem renList_length {rt : TRen} {Ts : List Ty} : (Ty.renList rt Ts).length = Ts.length := by
  rw [Ty.renList_eq_map]; simp

theorem renList_append {rt : TRen} {Ts Us : List Ty} :
    Ty.renList rt (Ts ++ Us) = Ty.renList rt Ts ++ Ty.renList rt Us := by
  simp [Ty.renList_eq_map]

theorem renList_bind {rt : TRen} {Dl : Bounds} {Us Ts : List Ty} (hl : Us.length = Dl.length)
    (hT : forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X (dom Dl)) :
    Ty.renList rt (Ty.substList (bind Dl Us) Ts) = Ty.substList (bind Dl (Ty.renList rt Us)) Ts := by
  rw [Ty.renList_subst, Ty.renList_subst]
  exact substList_bind_comp hl hT

theorem ren_bind {rt : TRen} {Dl : Bounds} {Us : List Ty} {T : Ty} (hl : Us.length = Dl.length)
    (hT : forall X, List.Mem X T.ftv -> List.Mem X (dom Dl)) :
    (T.subst (bind Dl Us)).ren rt = T.subst (bind Dl (Ty.renList rt Us)) := by
  rw [Ty.ren_subst, Ty.renList_subst]
  exact subst_bind_comp hl hT

abbrev BRen (rt : TRen) (Delta Delta' : Bounds) : Prop :=
  forall b, List.Mem b Delta -> List.Mem { X := rn rt b.X, T := b.T.ren rt } Delta'

theorem BRen.ctx {rt : TRen} {Delta Delta' : Bounds} (h : BRen rt Delta Delta') : RenCtx Delta Delta' (tS rt) :=
  fun b hb => Exists.intro (rn rt b.X) (And.intro lookup_tS (by rw [<- Ty.ren_subst]; exact h b hb))

theorem Sub.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {T1 T2 : Ty} (h : Sub d Delta T1 T2) : Sub d Delta' (T1.ren rt) (T2.ren rt) := by
  rw [Ty.ren_subst, Ty.ren_subst]; exact Sub.subst hd hb.ctx.sub h

theorem Kind.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {T : Ty} (h : Kind d Delta T) : Kind d Delta' (T.ren rt) := by
  rw [Ty.ren_subst]; exact Kind.subst hd hb.ctx.sub hb.ctx.kind h

theorem Cast.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {T1 T2 : Ty} (h : Cast d Delta T1 T2) : Cast d Delta' (T1.ren rt) (T2.ren rt) := by
  rw [Ty.ren_subst, Ty.ren_subst]; exact Cast.ren hd hb.ctx h

theorem SubSeq.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {Ts Us : List Ty} (h : SubSeq d Delta Ts Us) : SubSeq d Delta' (Ty.renList rt Ts) (Ty.renList rt Us) := by
  rw [Ty.renList_subst, Ty.renList_subst]; exact SubSeq.subst hd hb.ctx.sub h

theorem KindSeq.renT {d : Decls} (hd : DeclOk d) {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta')
    {Ts : List Ty} (h : KindSeq d Delta Ts) : KindSeq d Delta' (Ty.renList rt Ts) := by
  intro T hT
  rw [Ty.renList_eq_map] at hT
  rcases List.mem_map.mp hT with ⟨U, hU⟩; rw [<- hU.2]; exact Kind.renT hd hb (h U hU.1)

theorem Scope.renT {d : Decls} {rt : TRen} {C : ClassName} {Ts : List Ty} {Delta0 : Bounds} {Ts0 : List Ty}
    (h : Scope d (.cls C Ts) Delta0 Ts0) : Scope d (.cls C (Ty.renList rt Ts)) Delta0 (Ty.renList rt Ts0) := by
  have := h.subst (s := tS rt)
  rw [Ty.renList_subst, Ty.renList_subst]
  exact this

theorem abs_ren {rt : TRen} : forall {Fs : List Funnel}, abs (Fs.map (Funnel.ren rt)) = Ty.renList rt (abs Fs)
  | [] => rfl
  | F :: Fs => by
    simp only [abs, List.map_cons, Ty.renList] at |-
    rw [show List.map Funnel.abs (List.map (Funnel.ren rt) Fs) = abs (Fs.map (Funnel.ren rt)) from rfl, abs_ren]
    cases F with
    | ground G => simp only [Funnel.ren, Funnel.abs]; rw [GTy.ren_ty]; rfl
    | funnel X => rfl

theorem Pairing.renT {rt : TRen} {Delta Delta' : Bounds} (hb : BRen rt Delta Delta') {Fs : List Funnel}
    {Ts : List Ty} {Dp : Bounds} {Tp : List Ty} (h : Pairing Delta Fs Ts Dp Tp) :
    Pairing Delta' (Fs.map (Funnel.ren rt)) (Ty.renList rt Ts)
      (Dp.map fun b => ({ X := rn rt b.X, T := b.T.ren rt } : Bound)) (Ty.renList rt Tp) := by
  induction h with
  | nil => exact Pairing.nil
  | funnel hm _ ih => exact Pairing.funnel (hb _ hm) ih
  | @ground G Fs Ts Delta0 Ts0 _ ih =>
    simp only [List.map_cons, Funnel.ren, Ty.renList]
    rw [GTy.ren_ty]
    exact Pairing.ground ih

mutual
theorem Ty.ftv_subst_sub {s : TSubst} {A : List TVarName} : forall {T : Ty},
    (forall Y, List.Mem Y T.ftv -> forall X, List.Mem X ((Ty.var Y).subst s).ftv -> List.Mem X A) ->
    forall X, List.Mem X (T.subst s).ftv -> List.Mem X A
  | .var Y, h, X, hX => h Y (List.Mem.head _) X hX
  | .cls _ _, h, X, hX => Ty.ftvList_subst_sub h X hX
theorem Ty.ftvList_subst_sub {s : TSubst} {A : List TVarName} : forall {Ts : List Ty},
    (forall Y, List.Mem Y (Ty.ftvList Ts) -> forall X, List.Mem X ((Ty.var Y).subst s).ftv -> List.Mem X A) ->
    forall X, List.Mem X (Ty.ftvList (Ty.substList s Ts)) -> List.Mem X A
  | [], _, _, h => by cases h
  | T :: Ts, h, X, hX => by
    simp only [Ty.substList, Ty.ftvList, listMem_iff, List.mem_append] at hX h
    rcases hX with hX | hX
    . exact Ty.ftv_subst_sub (fun Y hY => h Y (Or.inl hY)) X hX
    . exact Ty.ftvList_subst_sub (fun Y hY => h Y (Or.inr hY)) X hX
end

theorem ftv_var_subst {s : TSubst} {Y X : TVarName} {U : Ty} (hl : List.lookup Y s = some U)
    (hX : List.Mem X ((Ty.var Y).subst s).ftv) : List.Mem X U.ftv := by
  simp only [Ty.subst, hl, Option.getD_some] at hX
  exact hX

theorem mem_bind_snd {A : Type} {Dl : Bounds} {Us : List A} {Y : TVarName} {U : A} (h : List.Mem (Y, U) (bind Dl Us)) :
    List.Mem U Us := (List.of_mem_zip h).2

theorem mem_bindF_snd : forall {Fs : List Funnel} {Us : List Ty} {Y : TVarName} {U : Ty},
    List.Mem (Y, U) (bindF Fs Us) -> List.Mem U Us
  | [], _, _, _, h => by simp [bindF] at h
  | _ :: _, [], _, _, h => by simp [bindF] at h
  | F :: Fs, U' :: Us, Y, U, h => by
    cases F with
    | funnel X =>
      have e : bindF (.funnel X :: Fs) (U' :: Us) = (X, U') :: bindF Fs Us := by simp [bindF]
      rw [e] at h
      cases h with
      | head => exact List.Mem.head _
      | tail _ h => exact List.Mem.tail _ (mem_bindF_snd h)
    | ground G =>
      have e : bindF (.ground G :: Fs) (U' :: Us) = bindF Fs Us := by simp [bindF]
      rw [e] at h
      exact List.Mem.tail _ (mem_bindF_snd h)

theorem ftv_bind_sub {Dl : Bounds} {Us : List Ty} {L : List Ty} (hl : Us.length = Dl.length)
    (hL : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (dom Dl)) :
    forall X, List.Mem X (Ty.ftvList (Ty.substList (bind Dl Us) L)) -> List.Mem X (Ty.ftvList Us) := by
  refine Ty.ftvList_subst_sub (fun Y hY X hX => ?_)
  cases bind_lookup_some hl (hL Y hY) with
  | intro U hU => exact Ty.mem_ftvList.mpr (Exists.intro U (And.intro (mem_bind_snd (lookup_mem hU)) (ftv_var_subst hU hX)))

theorem ftv_bindF_sub {Fs : List Funnel} {Us : List Ty} {L : List Ty} (hl : Us.length = Fs.length)
    (hL : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (domF Fs)) :
    forall X, List.Mem X (Ty.ftvList (Ty.substList (bindF Fs Us) L)) -> List.Mem X (Ty.ftvList Us) := by
  refine Ty.ftvList_subst_sub (fun Y hY X hX => ?_)
  cases bindF_lookup_some hl (hL Y hY) with
  | intro U hU => exact Ty.mem_ftvList.mpr (Exists.intro U (And.intro (mem_bindF_snd (lookup_mem hU)) (ftv_var_subst hU hX)))

theorem Sub.inv_subst {d : Decls} (hd : DeclOk d) {Delta Delta2 : Bounds} {s : TSubst} {A : List TVarName}
    {T1 T' : Ty} (h : Sub d Delta T1 T') : forall {C : ClassName} {Ts : List Ty}, T1 = .cls C (Ty.substList s Ts) ->
    (forall X, List.Mem X (Ty.ftvList Ts) -> List.Mem X A) ->
    exists T0, T' = T0.subst s /\ Sub d Delta2 (.cls C Ts) T0 /\ forall X, List.Mem X T0.ftv -> List.Mem X A := by
  induction h with
  | subRefl =>
    intro C Ts he hA
    subst he
    exact Exists.intro (.cls C Ts) (And.intro (by simp only [Ty.subst]) (And.intro Sub.subRefl hA))
  | @subInherit D Ts0 T' hD hl _ ih =>
    intro C Ts he hA
    simp only [Ty.cls.injEq] at he
    have e1 := he.1
    have e2 := he.2
    subst e1 e2
    have hl' : Ts.length = D.bounds.length := by rw [<- hl, substList_length]
    have heq : (Ty.cls D.C' D.Ts).subst (bind D.bounds (Ty.substList s Ts)) =
        .cls D.C' (Ty.substList s (Ty.substList (bind D.bounds Ts) D.Ts)) := by
      simp only [Ty.subst]
      rw [substList_bind_comp hl' (hd.supD D hD)]
    cases ih heq (fun X hX => ftv_bind_sub hl' (hd.supD D hD) X hX |> fun h => Ty.mem_ftvList.mp h |> fun h => by
        cases h with | intro U hU => exact hA X (Ty.mem_ftvList.mpr (Exists.intro U hU))) with
    | intro T0 h0 =>
      refine Exists.intro T0 (And.intro h0.1 (And.intro (Sub.subInherit hD hl' ?_) h0.2.2))
      exact h0.2.1
  | @subInheritLocal C0 Fs C' Ts' es Ms Ts0 T' hD hl _ ih =>
    intro C Ts he hA
    simp only [Ty.cls.injEq] at he
    have e1 := he.1
    have e2 := he.2
    subst e1 e2
    have hl' : Ts.length = Fs.length := by rw [<- hl, substList_length]
    have hcl := hd.supL _ _ _ _ _ _ hD
    have heq : (Ty.cls C' Ts').subst (bindF Fs (Ty.substList s Ts)) =
        .cls C' (Ty.substList s (Ty.substList (bindF Fs Ts) Ts')) := by
      simp only [Ty.subst]
      rw [substList_eq_map (Us := Ts'), substList_eq_map (Us := Ty.substList (bindF Fs Ts) Ts'),
        substList_eq_map (Us := Ts'), List.map_map]
      congr 1
      apply List.map_congr_left
      intro T hT
      show _ = (T.subst (bindF Fs Ts)).subst s
      exact (subst_bindF_comp hl' (fun X hX => hcl X (Ty.mem_ftvList.mpr (Exists.intro T (And.intro hT hX))))).symm
    rcases ih heq (fun X hX => by exact hA X (ftv_bindF_sub hl' hcl X hX)) with ⟨T0, h0⟩
    refine Exists.intro T0 (And.intro h0.1 (And.intro (Sub.subInheritLocal hD hl' ?_) h0.2.2))
    exact h0.2.1
  | subVar _ _ _ =>
    simp_all

theorem map_zip_fst {A B C : Type} {f : A -> C} : forall {l : List A} {l' : List B}, l'.length = l.length ->
    (l.zip l').map (fun p => f p.1) = l.map f
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [map_zip_fst (by simpa using h)]

theorem renList_subst_gen {rt : TRen} {s : TSubst} {L : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList L) -> List.Mem X (s.map Prod.fst)) :
    Ty.renList rt (Ty.substList s L) = Ty.substList (s.map fun p => (p.1, p.2.ren rt)) L := by
  rw [Ty.renList_subst, Ty.substList_comp (fun X hX => var_subst_comp_of_some (lookup_isSome (h X hX)))]
  simp only [Ty.ren_subst]

theorem map_rn_zip : forall {xs ys : List TVarName} {r : TRen}, xs.Nodup -> xs.length = ys.length ->
    xs.map (rn (xs.zip ys ++ r)) = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, r, hn, hl => by
    simp only [List.zip_cons_cons, List.cons_append, List.map_cons, rn_cons_eq]
    have hn' := List.nodup_cons.mp hn
    have ih := map_rn_zip (r := r) hn'.2 (by simpa using hl)
    have e : xs.map (rn ((x, y) :: (xs.zip ys ++ r))) = xs.map (rn (xs.zip ys ++ r)) := by
      apply List.map_congr_left
      intro z hz
      have hzx : Not (z = x) := fun e => hn'.1 (by rw [<- e]; exact hz)
      exact rn_cons_ne hzx
    rw [e, ih]

theorem ren_vars {xs ys : List TVarName} {r : TRen} (hn : xs.Nodup) (hl : xs.length = ys.length) :
    (vars xs).map (Ty.ren (xs.zip ys ++ r)) = vars ys := by
  have e := map_rn_zip (r := r) hn hl
  simp only [vars, List.map_map]
  conv => rhs; rw [<- e]
  rw [List.map_map]
  rfl

theorem ren_disj {Xs Ys : List TVarName} {r : TRen} {Ts : List Ty}
    (h : forall X, List.Mem X (Ty.ftvList Ts) -> Not (List.Mem X Xs)) :
    Ts.map (Ty.ren (Xs.zip Ys ++ r)) = Ty.renList r Ts := by
  rw [Ty.renList_eq_map]
  apply List.map_congr_left
  intro T hT
  exact Ty.ren_congr (fun X hX => rn_zip_not_mem (h X (Ty.mem_ftvList.mpr (Exists.intro T (And.intro hT hX)))))

theorem declMeth_closed {d : Decls} (hwf : WFDecls d) (hok : DeclsOk d) {k : K} (hk : Declared d k)
    {Dl : Bounds} {T0 : Ty} {m : MethName} {ps : List VarDecl} {e : Expr} (hM : List.Mem (Method.mk Dl T0 m ps e) k.Ms) :
    (forall X, List.Mem X (Ty.ftvList (cod Dl)) -> List.Mem X (k.gvars ++ dom Dl)) /\
      (forall X, List.Mem X (Ty.ftvList (T0 :: ps.map VarDecl.T)) -> List.Mem X (k.gvars ++ dom Dl)) := by
  rcases scopeExists hwf hok hk with ⟨Dk, Tk, hs⟩
  rcases scopeFacts hwf hok hs with ⟨k', hk'⟩
  have hname : k'.name = k.name := by
    rcases hk'.2.1 with ⟨Us, hUs⟩
    rcases K.generic_name k with ⟨Vs, hVs⟩; rw [hVs] at hUs; simp only [Ty.cls.injEq] at hUs; exact hUs.1.symm
  have ek := Declared.unique hwf hk'.1 hk hname
  subst ek
  rcases hk'.2.2.meths _ hM with ⟨gamma, hmo⟩
  have hmi := methodOk_inv hmo
  rw [<- hk'.2.2.gv, <- dom_append]
  refine And.intro ?_ ?_
  . intro X hX
    rcases Ty.mem_ftvList.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.1 T hT.1) X hT.2
  . intro X hX
    rcases Ty.mem_ftvList.mp hX with ⟨T, hT⟩; exact Kind.ftv (hmi.2.1 T hT.1) X hT.2

end Funnelling
