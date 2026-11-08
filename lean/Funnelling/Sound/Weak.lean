import Funnelling.Sound.GammaL

open Funnelling.SoundSimp

namespace Funnelling

theorem Pairing.mono {Delta Delta2 : Bounds} (hs : Sub1 Delta Delta2) {Fs : List Funnel} {Ts : List Ty}
    {D0 : Bounds} {T0 : List Ty} (h : Pairing Delta Fs Ts D0 T0) : Pairing Delta2 Fs Ts D0 T0 := by
  induction h with
  | nil => exact Pairing.nil
  | funnel hm _ ih => exact Pairing.funnel (hs _ hm) ih
  | ground _ ih => exact Pairing.ground ih

theorem KindSeq.mono {d : Decls} {Delta Delta2 : Bounds} (hs : Sub1 Delta Delta2) {Ts : List Ty}
    (h : KindSeq d Delta Ts) : KindSeq d Delta2 Ts := fun T hT => (h T hT).mono hs

theorem SubSeq.mono {d : Decls} {Delta Delta2 : Bounds} (hs : Sub1 Delta Delta2) {Ts Us : List Ty}
    (h : SubSeq d Delta Ts Us) : SubSeq d Delta2 Ts Us := by
  induction h with
  | nil => exact Seq2.nil
  | cons h1 _ ih => exact Seq2.cons (h1.mono hs) ih

theorem Cast.mono {d : Decls} {Delta Delta2 : Bounds} (hs : Sub1 Delta Delta2) {T0 T : Ty}
    (h : Cast d Delta T0 T) : Cast d Delta2 T0 T := by
  induction h with
  | castUp h1 => exact Cast.castUp (h1.mono hs)
  | castVar hm _ ih => exact Cast.castVar (hs _ hm) ih
  | castDown h1 h2 h3 h4 => exact Cast.castDown (h1.mono hs) h2 h3 h4

abbrev innerG (gamma : Gamma) (Fs : List Funnel) (C : ClassName) : Gamma :=
  withoutThis (restrict gamma (Ty.ftvList (abs Fs))) ++ [{ T := .cls C (abs Fs), x := this }]

theorem innerG_sub {gamma gamma2 : Gamma} (h : Sub1 gamma gamma2) (Fs : List Funnel) (C : ClassName) :
    Sub1 (innerG gamma Fs C) (innerG gamma2 Fs C) := by
  intro y hy
  simp only [innerG, withoutThis, restrict, listMem_iff, List.mem_append, List.mem_filter, List.mem_singleton] at hy |-
  rcases hy with hy | hy
  . exact Or.inl (And.intro (And.intro (h y hy.1.1) hy.1.2) hy.2)
  . exact Or.inr hy

theorem innerG_nodup {gamma : Gamma} (h : (gdom gamma).Nodup) (Fs : List Funnel) (C : ClassName) :
    (gdom (innerG gamma Fs C)).Nodup := by
  simp only [innerG, gdom, List.map_append, List.map_cons, List.map_nil]
  apply List.nodup_append.mpr
  refine And.intro (gdom_filter_nodup (gdom_filter_nodup h)) (And.intro (by simp) ?_)
  intro a ha b hb e
  simp only [List.mem_singleton] at hb
  subst hb
  simp only [List.mem_map, withoutThis, List.mem_filter] at ha
  rcases ha with ⟨y, hy⟩
  have := hy.1.2
  rw [hy.2, e] at this
  simp at this

theorem innerG_dom {gamma : Gamma} {xs : List VarName} (h : Sub1 (gdom gamma) xs) (Fs : List Funnel) (C : ClassName) :
    Sub1 (gdom (innerG gamma Fs C)) (this :: xs.filter fun x => x != this) := by
  intro y hy
  simp only [innerG, gdom, withoutThis, restrict, listMem_iff, List.map_append, List.mem_append, List.mem_map,
    List.mem_filter, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy |-
  rcases hy with hy | hy
  . rcases hy with ⟨z, hz⟩
    right
    refine And.intro ?_ ?_
    . rw [<- hz.2]; exact h _ (List.mem_map_of_mem (f := VarDecl.x) hz.1.1.1)
    . rw [<- hz.2]; exact hz.1.2
  . left; exact hy

theorem gdom_append_single {gamma : Gamma} {T : Ty} {x : VarName} :
    gdom (gamma ++ [{ T := T, x := x }]) = gdom gamma ++ [x] := by simp [gdom]

theorem nodup_snoc {l : List VarName} {x : VarName} (h : l.Nodup) (hx : Not (List.Mem x l)) : (l ++ [x]).Nodup := by
  apply List.nodup_append.mpr
  refine And.intro h (And.intro (by simp) ?_)
  intro a ha b hb e
  simp only [List.mem_singleton] at hb
  subst hb; subst e
  exact hx ha

theorem scope_snoc {gamma : Gamma} {xs : List VarName} {T : Ty} {x : VarName} (h : Sub1 (gdom gamma) xs) :
    Sub1 (gdom (gamma ++ [{ T := T, x := x }])) (x :: xs) := by
  rw [gdom_append_single]
  intro z hz
  simp only [listMem_iff, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | hz
  . exact List.Mem.tail _ (h z hz)
  . rw [hz]; exact List.Mem.head _

theorem scope_params {gamma : Gamma} {xs : List VarName} {ps : List VarDecl} (h : Sub1 (gdom gamma) (this :: xs)) :
    Sub1 (gdom (gamma ++ ps)) (this :: xs ++ ps.map VarDecl.x) := by
  intro z hz
  simp only [gdom, List.map_append, listMem_iff, List.mem_append] at hz
  rcases hz with hz | hz
  . exact List.mem_append_left _ (h z hz)
  . exact List.mem_append_right _ hz

theorem nodup_params {gamma : Gamma} {xs : List VarName} {ps : List VarDecl} (n1 : (gdom gamma).Nodup)
    (sc : Sub1 (gdom gamma) (this :: xs)) (hp : (ps.map VarDecl.x).Nodup) (ht : Not (List.Mem this (ps.map VarDecl.x)))
    (hn : (ps.map VarDecl.x).all (fun x => !(xs.contains x)) = true) : (gdom (gamma ++ ps)).Nodup := by
  simp only [gdom, List.map_append]
  apply List.nodup_append.mpr
  refine And.intro n1 (And.intro hp ?_)
  intro a ha b hb e
  subst e
  cases sc a ha with
  | head => exact ht hb
  | tail _ h => exact not_mem_of_all_not_contains hn hb h

end Funnelling