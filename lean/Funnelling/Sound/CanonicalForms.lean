import Funnelling.Sound.SubtypingKinding

open Funnelling.SoundSimp

namespace Funnelling

theorem object_declared {d : Decls} (hwf : WFDecls d) : exists D, Declared d (.dec D) /\ D.C = Object /\
    D.bounds = [] /\ D.C' = Object /\ D.Ts = [] /\ D.Ms = [] /\ D.Ss = [] := by
  rcases hwf.2.2.2.2.2.2.2.2.1.1 with ⟨D, hD⟩
  exact Exists.intro D (And.intro (Declared.dec hD.1) (And.intro hD.2.1
    (And.intro (by simpa using hD.2.2.1) (And.intro hD.2.2.2.1 (And.intro (by simpa using hD.2.2.2.2.1)
    (And.intro (by simpa using hD.2.2.2.2.2.1) (by simpa using hD.2.2.2.2.2.2)))))))

theorem kind_object {d : Decls} (hwf : WFDecls d) {Delta : Bounds} : Kind d Delta (.cls Object []) := by
  rcases object_declared hwf with ⟨D, hD⟩
  have hs : Scope d (.cls D.C []) D.bounds [] := Scope.dec hD.1
  rw [hD.2.1, hD.2.2.1] at hs
  exact Kind.wfClass hs (fun _ h => by cases h) rfl Seq2.nil

theorem value_typing {d : Decls} (hwf : WFDecls d) {v : Value} {T : Ty} (h : Typing d [] [] v.expr T) :
    Up d [] (typeOf v) T /\ Typing d [] [] v.expr (typeOf v) /\ Kind d [] (typeOf v) := by
  cases v with
  | new C Gs vs =>
    simp only [Value.expr] at h |-
    rcases inv_new h rfl with h1 | h1
    . have hG : Gs = [] := by cases Gs <;> simp_all [GTy.tys]
      have hv : vs = [] := by cases vs <;> simp_all [Value.exprs]
      subst hG hv
      rw [h1.1]
      exact And.intro h1.2.2.2 (And.intro Typing.newObject (kind_object hwf))
    . rcases h1 with ⟨w, hw⟩
      have hn := hw.name
      refine And.intro (by rw [<- hn]; exact hw.up) (And.intro ?_ (by rw [<- hn]; exact Kind.mono (fun _ h => h) hw.kind))
      rw [<- hn, hw.split]
      exact Typing.newTop hw.decl hw.kind hw.len hw.fields hw.sup
  | newLocal C Gs C' Gs' vs Ms =>
    simp only [Value.expr] at h |-
    rcases inv_local h rfl with ⟨w, hw⟩
    have hD := pairing_ground_nil hw.pair
    have hk := hw.kindC
    rw [hD, abs_ground] at hk
    have hup := hw.up
    rw [abs_ground] at hup
    refine And.intro hup (And.intro ?_ hk)
    have := Typing.newLocal hw.cons hw.pair hw.closedB hw.kindC hw.kindS hw.tyNew hw.meths hw.over
    rwa [abs_ground] at this

theorem Sub.top_target {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} (hD : Declared d (.dec D))
    {Ts : List Ty} {C0 : ClassName} {Ts0 : List Ty} (h : Sub d Delta (.cls D.C Ts) (.cls C0 Ts0)) :
    exists D0, Declared d (.dec D0) /\ D0.C = C0 := by
  generalize he : Ty.cls D.C Ts = T at h
  generalize ht : Ty.cls C0 Ts0 = T' at h
  induction h generalizing D Ts with
  | subRefl =>
    rw [<- ht] at he
    simp only [Ty.cls.injEq] at he
    exact Exists.intro D (And.intro hD he.1)
  | @subInherit D' Ts0' T' hD' hl _ ih =>
    rcases Declared.super hwf hD' with ⟨D'', hD''⟩
    exact ih hD''.1 (Ts := Ty.substList (bind D'.bounds Ts0') D'.Ts) (by simp only [Ty.subst]; rw [hD''.2]; rfl) ht
  | subInheritLocal hD' _ _ =>
    simp only [Ty.cls.injEq] at he
    exact absurd (Declared.dec_loc hwf hD hD' he.1) id
  | subVar => cases he

theorem lookup_zip_nodup {A B : Type} [DecidableEq A] : forall {xs : List A} {ys : List B} {x : A} {y : B},
    xs.Nodup -> List.Mem (x, y) (xs.zip ys) -> List.lookup x (xs.zip ys) = some y
  | [], _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | a :: xs, b :: ys, x, y, hn, h => by
    simp only [List.zip_cons_cons] at h |-
    cases h with
    | head => exact lookup_cons_eq
    | tail _ h =>
      have hx : Not (x = a) := by
        intro e; subst e
        exact (List.nodup_cons.mp hn).1 (List.of_mem_zip h).1
      rw [lookup_cons_ne hx]
      exact lookup_zip_nodup (List.nodup_cons.mp hn).2 h

theorem bounds_sat_aux {d : Decls} {Delta : Bounds} {s : TSubst} : forall {Dl : Bounds} {Ts : List Ty},
    Ts.length = Dl.length -> SubSeq d Delta Ts (Ty.substList s (cod Dl)) -> (forall T, List.Mem T Ts -> Kind d Delta T) ->
    forall b, List.Mem b Dl -> exists T, List.Mem (b.X, T) ((dom Dl).zip Ts) /\ Sub d Delta T (b.T.subst s) /\ Kind d Delta T
  | [], _, _, _, _, b, hb => by cases hb
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | b0 :: Dl, T0 :: Ts, hl, hs, hk, b, hb => by
    cases hs with
    | cons h1 h2 =>
      cases hb with
      | head => exact Exists.intro T0 (And.intro (List.Mem.head _) (And.intro h1 (hk T0 (List.Mem.head _))))
      | tail _ hb =>
        cases bounds_sat_aux (by simpa using hl) h2 (fun T hT => hk T (List.Mem.tail _ hT)) b hb with
        | intro T hT => exact Exists.intro T (And.intro (List.Mem.tail _ hT.1) hT.2)

theorem bounds_sat {d : Decls} {Delta Dl : Bounds} {Ts : List Ty} (hn : (dom Dl).Nodup)
    (hl : Ts.length = Dl.length) (hs : SubSeq d Delta Ts (Ty.substList (bind Dl Ts) (cod Dl)))
    (hk : forall T, List.Mem T Ts -> Kind d Delta T) :
    forall b, List.Mem b Dl -> Sub d Delta ((Ty.var b.X).subst (bind Dl Ts)) (b.T.subst (bind Dl Ts)) /\
      Kind d Delta ((Ty.var b.X).subst (bind Dl Ts)) := by
  intro b hb
  rcases bounds_sat_aux hl hs hk b hb with ⟨T, hT⟩
  have e : (Ty.var b.X).subst (bind Dl Ts) = T := by
    simp only [Ty.subst, bind, lookup_zip_nodup hn hT.1, Option.getD_some]
  rw [e]
  exact hT.2

theorem kind_dec_args {d : Decls} (hwf : WFDecls d) {Delta : Bounds} {D : Dec} (hD : Declared d (.dec D))
    {Ts : List Ty} (h : Kind d Delta (.cls D.C Ts)) :
    Ts.length = D.bounds.length /\ forall b, List.Mem b D.bounds ->
      Sub d Delta ((Ty.var b.X).subst (bind D.bounds Ts)) (b.T.subst (bind D.bounds Ts)) /\
      Kind d Delta ((Ty.var b.X).subst (bind D.bounds Ts)) := by
  cases h with
  | wfClass h1 h2 h3 h4 =>
    have e := Scope.dec_eq hwf hD h1
    have e1 := e.1
    have e2 := e.2
    subst e1 e2
    have hn : (dom D.bounds).Nodup := hwf.2.2.2.2.1 D.bounds (by
      simp only [listMem_iff, List.mem_append, List.mem_map]
      exact Or.inl (Exists.intro D (And.intro hD.dec_mem rfl)))
    exact And.intro h3 (bounds_sat hn h3 h4 h2)

end Funnelling
