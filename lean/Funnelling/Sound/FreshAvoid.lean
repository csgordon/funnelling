import Funnelling.Sound.WFSubst

open Funnelling.SoundSimp

namespace Funnelling.High

class Nm (A : Type) where
  nm : A -> String
  ofName : String -> A
  nm_mk : forall s, nm (ofName s) = s

instance : Nm VarName := ⟨VarName.name, VarName.mk, fun _ => rfl⟩

instance : Nm TVarName := ⟨TVarName.name, TVarName.mk, fun _ => rfl⟩

def fresh {A : Type} [Nm A] (L : List A) (k : Nat) : A :=
  Nm.ofName (String.ofList (List.replicate ((L.map fun v => (Nm.nm v).length).sum + k + 1) 'a'))

theorem fresh_len {A : Type} [Nm A] (L : List A) (k : Nat) :
    (Nm.nm (fresh L k)).length = (L.map fun v => (Nm.nm v).length).sum + k + 1 := by
  simp [fresh, Nm.nm_mk]

theorem len_le_sum {A : Type} [Nm A] : forall {L : List A} {v : A}, List.Mem v L ->
    (Nm.nm v).length <= (L.map fun v => (Nm.nm v).length).sum
  | [], _, h => by cases h
  | _ :: _, _, h => by
    cases h with
    | head => simp
    | tail _ h => have := len_le_sum h; simp; omega

theorem fresh_not_mem {A : Type} [Nm A] (L : List A) (k : Nat) : Not (List.Mem (fresh L k) L) := fun h => by
  have h1 := len_le_sum h
  rw [fresh_len] at h1
  omega

theorem fresh_inj {A : Type} [Nm A] (L : List A) : Function.Injective (fresh L) := fun k j h => by
  have := congrArg (fun v => (Nm.nm v).length) h
  simp only [fresh_len] at this
  omega

def frs {A : Type} [Nm A] (L : List A) (d n : Nat) : List A := (List.range n).map fun i => fresh L (d + i)

theorem frs_length {A : Type} [Nm A] {L : List A} {d n : Nat} : (frs L d n).length = n := by simp [frs]

theorem frs_mem {A : Type} [Nm A] {L : List A} {d n : Nat} {y : A} (h : List.Mem y (frs L d n)) :
    exists i, i < n /\ y = fresh L (d + i) := by
  rcases List.mem_map.mp h with ⟨i, hi, e⟩
  exact ⟨i, List.mem_range.mp hi, e.symm⟩

theorem frs_nodup {A : Type} [Nm A] {L : List A} {d n : Nat} : (frs L d n).Nodup :=
  List.Pairwise.map _ (fun a b h e => h (by have := fresh_inj L e; omega)) List.nodup_range

mutual
def Expr.fr (LV : List VarName) (LT : List TVarName) (rv : VRen) (rt : TRen) (d : Nat) : Expr -> Expr
  | .var x => .var (x.ren rv)
  | .call e Ts m es => .call (e.fr LV LT rv rt d) (Ty.renList rt Ts) m (Expr.frList LV LT rv rt d es)
  | .superCall e T Ts m es =>
    .superCall (e.fr LV LT rv rt d) (T.ren rt) (Ty.renList rt Ts) m (Expr.frList LV LT rv rt d es)
  | .field e f => .field (e.fr LV LT rv rt d) f
  | .new C Ts es => .new C (Ty.renList rt Ts) (Expr.frList LV LT rv rt d es)
  | .newLocal C Fs C' Ts es Ms =>
    .newLocal C (Fs.map (Funnel.ren rt)) C' (Ty.renList rt Ts) (Expr.frList LV LT rv rt d es)
      (Method.frList LV LT rv rt d Ms)
  | .ifInst e0 T x e1 e2 =>
    .ifInst (e0.fr LV LT rv rt d) (T.ren rt) (fresh LV d) (e1.fr LV LT ((x, fresh LV d) :: rv) rt (d + 1))
      (e2.fr LV LT rv rt d)
def Expr.frList (LV : List VarName) (LT : List TVarName) (rv : VRen) (rt : TRen) (d : Nat) :
    List Expr -> List Expr
  | [] => []
  | e :: es => e.fr LV LT rv rt d :: Expr.frList LV LT rv rt d es
def Method.fr (LV : List VarName) (LT : List TVarName) (rv : VRen) (rt : TRen) (d : Nat) : Method -> Method
  | .mk Delta T0 m ps e =>
    .mk ((Delta.zip (frs LT d Delta.length)).map fun p =>
          { X := p.2, T := p.1.T.ren ((dom Delta).zip (frs LT d Delta.length) ++ rt) })
      (T0.ren ((dom Delta).zip (frs LT d Delta.length) ++ rt)) m
      ((ps.zip (frs LV d ps.length)).map fun p =>
          { T := p.1.T.ren ((dom Delta).zip (frs LT d Delta.length) ++ rt), x := p.2 })
      (e.fr LV LT ((ps.map VarDecl.x).zip (frs LV d ps.length) ++ rv)
        ((dom Delta).zip (frs LT d Delta.length) ++ rt) (d + (Delta.length + ps.length)))
def Method.frList (LV : List VarName) (LT : List TVarName) (rv : VRen) (rt : TRen) (d : Nat) :
    List Method -> List Method
  | [] => []
  | M :: Ms => M.fr LV LT rv rt d :: Method.frList LV LT rv rt d Ms
end

mutual
theorem Expr.fr_ren {LV : List VarName} {LT : List TVarName} :
    forall (e : Expr) (rv : VRen) (rt : TRen) (d : Nat), RenE rv rt e (e.fr LV LT rv rt d)
  | .var _, _, _, _ => RenE.var
  | .call e _ _ es, rv, rt, d => RenE.call (Expr.fr_ren e rv rt d) (Expr.frList_ren es rv rt d)
  | .superCall e _ _ _ es, rv, rt, d => RenE.superCall (Expr.fr_ren e rv rt d) (Expr.frList_ren es rv rt d)
  | .field e _, rv, rt, d => RenE.field (Expr.fr_ren e rv rt d)
  | .new _ _ es, rv, rt, d => RenE.new (Expr.frList_ren es rv rt d)
  | .newLocal _ _ _ _ es Ms, rv, rt, d =>
    RenE.newLocal (Expr.frList_ren es rv rt d) (Method.frList_ren Ms rv rt d)
  | .ifInst e0 _ _ e1 e2, rv, rt, d =>
    RenE.ifInst (Expr.fr_ren e0 rv rt d) (Expr.fr_ren e1 _ rt (d + 1)) (Expr.fr_ren e2 rv rt d)
theorem Expr.frList_ren {LV : List VarName} {LT : List TVarName} :
    forall (es : List Expr) (rv : VRen) (rt : TRen) (d : Nat), RenEs rv rt es (Expr.frList LV LT rv rt d es)
  | [], _, _, _ => RenEs.nil
  | e :: es, rv, rt, d => RenEs.cons (Expr.fr_ren e rv rt d) (Expr.frList_ren es rv rt d)
theorem Method.fr_ren {LV : List VarName} {LT : List TVarName} :
    forall (M : Method) (rv : VRen) (rt : TRen) (d : Nat), RenM rv rt M (M.fr LV LT rv rt d)
  | .mk _ _ _ _ e, _, _, _ => RenM.mk frs_length frs_length (Expr.fr_ren e _ _ _)
theorem Method.frList_ren {LV : List VarName} {LT : List TVarName} :
    forall (Ms : List Method) (rv : VRen) (rt : TRen) (d : Nat), RenMs rv rt Ms (Method.frList LV LT rv rt d Ms)
  | [], _, _, _ => RenMs.nil
  | M :: Ms, rv, rt, d => RenMs.cons (Method.fr_ren M rv rt d) (Method.frList_ren Ms rv rt d)
end

abbrev At {A : Type} [Nm A] (L : List A) (d : Nat) (y : A) : Prop := exists k, d <= k /\ y = fresh L k

theorem At.mono {A : Type} [Nm A] {L : List A} {d d' : Nat} {y : A} (h : d <= d') : At L d' y -> At L d y :=
  fun ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

theorem frs_at {A : Type} [Nm A] {L : List A} {d n : Nat} {y : A} (h : List.Mem y (frs L d n)) : At L d y := by
  rcases frs_mem h with ⟨i, _, e⟩
  exact ⟨d + i, by omega, e⟩

mutual
theorem Expr.fr_vb {LV : List VarName} {LT : List TVarName} :
    forall (e : Expr) {rv : VRen} {rt : TRen} {d : Nat} {y : VarName},
    List.Mem y (e.fr LV LT rv rt d).vbinders -> At LV d y
  | .var _, _, _, _, _, h => by simp [Expr.fr, Expr.vbinders] at h
  | .call e _ _ es, _, _, _, _, h => (List.mem_append.mp h).elim (Expr.fr_vb e) (Expr.frList_vb es)
  | .superCall e _ _ _ es, _, _, _, _, h => (List.mem_append.mp h).elim (Expr.fr_vb e) (Expr.frList_vb es)
  | .field e _, _, _, _, _, h => Expr.fr_vb e h
  | .new _ _ es, _, _, _, _, h => Expr.frList_vb es h
  | .newLocal _ _ _ _ es Ms, _, _, _, _, h => (List.mem_append.mp h).elim (Expr.frList_vb es) (Method.frList_vb Ms)
  | .ifInst e0 _ _ e1 e2, _, _, d, _, h => by
    simp only [Expr.fr, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons] at h
    rcases h with ((h | h) | h) | h
    . exact ⟨d, Nat.le_refl _, h⟩
    . exact Expr.fr_vb e0 h
    . exact At.mono (Nat.le_succ d) (Expr.fr_vb e1 h)
    . exact Expr.fr_vb e2 h
theorem Expr.frList_vb {LV : List VarName} {LT : List TVarName} :
    forall (es : List Expr) {rv : VRen} {rt : TRen} {d : Nat} {y : VarName},
    List.Mem y (Expr.vbindersList (Expr.frList LV LT rv rt d es)) -> At LV d y
  | [], _, _, _, _, h => by simp [Expr.frList, Expr.vbindersList] at h
  | e :: es, _, _, _, _, h => (List.mem_append.mp h).elim (Expr.fr_vb e) (Expr.frList_vb es)
theorem Method.fr_vb {LV : List VarName} {LT : List TVarName} :
    forall (M : Method) {rv : VRen} {rt : TRen} {d : Nat} {y : VarName},
    List.Mem y (M.fr LV LT rv rt d).vbinders -> At LV d y
  | .mk _ _ _ _ e, _, _, _, _, h => by
    simp only [Method.fr, Method.vbinders] at h
    rw [names_renParams frs_length] at h
    exact (List.mem_append.mp h).elim frs_at (fun h => At.mono (Nat.le_add_right _ _) (Expr.fr_vb e h))
theorem Method.frList_vb {LV : List VarName} {LT : List TVarName} :
    forall (Ms : List Method) {rv : VRen} {rt : TRen} {d : Nat} {y : VarName},
    List.Mem y (Method.vbindersList (Method.frList LV LT rv rt d Ms)) -> At LV d y
  | [], _, _, _, _, h => by simp [Method.frList, Method.vbindersList] at h
  | M :: Ms, _, _, _, _, h => (List.mem_append.mp h).elim (Method.fr_vb M) (Method.frList_vb Ms)
end

mutual
theorem Expr.fr_tb {LV : List VarName} {LT : List TVarName} :
    forall (e : Expr) {rv : VRen} {rt : TRen} {d : Nat} {Y : TVarName},
    List.Mem Y (e.fr LV LT rv rt d).tbinders -> At LT d Y
  | .var _, _, _, _, _, h => by simp [Expr.fr, Expr.tbinders] at h
  | .call e _ _ es, _, _, _, _, h => (List.mem_append.mp h).elim (Expr.fr_tb e) (Expr.frList_tb es)
  | .superCall e _ _ _ es, _, _, _, _, h => (List.mem_append.mp h).elim (Expr.fr_tb e) (Expr.frList_tb es)
  | .field e _, _, _, _, _, h => Expr.fr_tb e h
  | .new _ _ es, _, _, _, _, h => Expr.frList_tb es h
  | .newLocal _ _ _ _ es Ms, _, _, _, _, h => (List.mem_append.mp h).elim (Expr.frList_tb es) (Method.frList_tb Ms)
  | .ifInst e0 _ _ e1 e2, _, _, d, _, h => by
    simp only [Expr.fr, Expr.tbinders, listMem_iff, List.mem_append] at h
    rcases h with (h | h) | h
    . exact Expr.fr_tb e0 h
    . exact At.mono (Nat.le_succ d) (Expr.fr_tb e1 h)
    . exact Expr.fr_tb e2 h
theorem Expr.frList_tb {LV : List VarName} {LT : List TVarName} :
    forall (es : List Expr) {rv : VRen} {rt : TRen} {d : Nat} {Y : TVarName},
    List.Mem Y (Expr.tbindersList (Expr.frList LV LT rv rt d es)) -> At LT d Y
  | [], _, _, _, _, h => by simp [Expr.frList, Expr.tbindersList] at h
  | e :: es, _, _, _, _, h => (List.mem_append.mp h).elim (Expr.fr_tb e) (Expr.frList_tb es)
theorem Method.fr_tb {LV : List VarName} {LT : List TVarName} :
    forall (M : Method) {rv : VRen} {rt : TRen} {d : Nat} {Y : TVarName},
    List.Mem Y (M.fr LV LT rv rt d).tbinders -> At LT d Y
  | .mk _ _ _ _ e, _, _, _, _, h => by
    simp only [Method.fr, Method.tbinders] at h
    rw [dom_renBounds frs_length] at h
    exact (List.mem_append.mp h).elim frs_at (fun h => At.mono (Nat.le_add_right _ _) (Expr.fr_tb e h))
theorem Method.frList_tb {LV : List VarName} {LT : List TVarName} :
    forall (Ms : List Method) {rv : VRen} {rt : TRen} {d : Nat} {Y : TVarName},
    List.Mem Y (Method.tbindersList (Method.frList LV LT rv rt d Ms)) -> At LT d Y
  | [], _, _, _, _, h => by simp [Method.frList, Method.tbindersList] at h
  | M :: Ms, _, _, _, _, h => (List.mem_append.mp h).elim (Method.fr_tb M) (Method.frList_tb Ms)
end

abbrev Below {A : Type} [Nm A] (L : List A) (d : Nat) (S : List A) : Prop :=
  forall y, List.Mem y S -> Not (At L d y)

theorem Below.mono {A : Type} [Nm A] {L : List A} {d d' : Nat} {T : List A} (h : d <= d') (hb : Below L d T) :
    Below L d' T := fun Y hY ha => hb Y hY (At.mono h ha)

theorem Below.ext {A : Type} [Nm A] {LV : List A} {d : Nat} {S : List A} (hb : Below LV d S) :
    Below LV (d + 1) (fresh LV d :: S) := by
  intro y hy ha
  cases hy with
  | head => rcases ha with ⟨k, hk, e⟩; have := fresh_inj LV e; omega
  | tail _ hy => exact hb y hy (At.mono (Nat.le_succ d) ha)

theorem Below.methV {LV : List VarName} {d n m : Nat} {S : List VarName} (ht : List.Mem this LV)
    (hb : Below LV d S) : Below LV (d + (n + m)) (this :: S ++ frs LV d m) := by
  intro y hy ha
  simp only [listMem_iff, List.mem_append, List.mem_cons] at hy
  rcases hy with (hy | hy) | hy
  . rcases ha with ⟨k, _, e⟩
    subst hy
    rw [e] at ht
    exact fresh_not_mem LV k ht
  . exact hb y hy (At.mono (by omega) ha)
  . rcases frs_mem hy with ⟨i, hi, e1⟩
    rcases ha with ⟨k, hk, e2⟩
    have := fresh_inj LV (e1.symm.trans e2)
    omega

theorem Below.meth {A : Type} [Nm A] {LT : List A} {d n m : Nat} {T : List A} (hb : Below LT d T) :
    Below LT (d + (n + m)) (T ++ frs LT d n) := by
  intro Y hY ha
  simp only [listMem_iff, List.mem_append] at hY
  rcases hY with hY | hY
  . exact hb Y hY (At.mono (by omega) ha)
  . rcases frs_mem hY with ⟨i, hi, e1⟩
    rcases ha with ⟨k, hk, e2⟩
    have := fresh_inj LT (e1.symm.trans e2)
    omega

theorem not_contains_of {A : Type} [DecidableEq A] {l : List A} {x : A} (h : Not (List.Mem x l)) :
    (!(l.contains x)) = true := by
  simpa using h

mutual
theorem Expr.fr_noShadow {LV : List VarName} {LT : List TVarName} (ht : List.Mem this LV) :
    forall (e : Expr) {rv : VRen} {rt : TRen} {d : Nat} {Tb : List TVarName} {Sb : List VarName},
    Below LV d Sb -> Below LT d Tb -> (e.fr LV LT rv rt d).noShadow Tb Sb = true
  | .var _, _, _, _, _, _, _, _ => rfl
  | .call e _ _ es, _, _, _, _, _, hS, hT => by
    simp only [Expr.fr, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.fr_noShadow ht e hS hT, Expr.frList_noShadow ht es hS hT⟩
  | .superCall e _ _ _ es, _, _, _, _, _, hS, hT => by
    simp only [Expr.fr, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.fr_noShadow ht e hS hT, Expr.frList_noShadow ht es hS hT⟩
  | .field e _, _, _, _, _, _, hS, hT => Expr.fr_noShadow ht e hS hT
  | .new _ _ es, _, _, _, _, _, hS, hT => Expr.frList_noShadow ht es hS hT
  | .newLocal _ _ _ _ es Ms, _, _, _, _, _, hS, hT => by
    simp only [Expr.fr, Expr.noShadow, Bool.and_eq_true]
    exact ⟨Expr.frList_noShadow ht es hS hT,
      Method.frList_noShadow ht Ms (fun y hy => hS y (List.mem_filter.mp hy).1) hT⟩
  | .ifInst e0 _ _ e1 e2, _, _, d, _, _, hS, hT => by
    simp only [Expr.fr, Expr.noShadow, Bool.and_eq_true]
    exact ⟨⟨⟨Expr.fr_noShadow ht e0 hS hT, not_contains_of (fun h => hS _ h ⟨d, Nat.le_refl _, rfl⟩)⟩,
      Expr.fr_noShadow ht e1 hS.ext (hT.mono (Nat.le_succ d))⟩, Expr.fr_noShadow ht e2 hS hT⟩
theorem Expr.frList_noShadow {LV : List VarName} {LT : List TVarName} (ht : List.Mem this LV) :
    forall (es : List Expr) {rv : VRen} {rt : TRen} {d : Nat} {Tb : List TVarName} {Sb : List VarName},
    Below LV d Sb -> Below LT d Tb -> Expr.noShadowList Tb Sb (Expr.frList LV LT rv rt d es) = true
  | [], _, _, _, _, _, _, _ => rfl
  | e :: es, _, _, _, _, _, hS, hT => by
    simp only [Expr.frList, Expr.noShadowList, Bool.and_eq_true]
    exact ⟨Expr.fr_noShadow ht e hS hT, Expr.frList_noShadow ht es hS hT⟩
theorem Method.fr_noShadow {LV : List VarName} {LT : List TVarName} (ht : List.Mem this LV) :
    forall (M : Method) {rv : VRen} {rt : TRen} {d : Nat} {Tb : List TVarName} {Sb : List VarName},
    Below LV d Sb -> Below LT d Tb -> (M.fr LV LT rv rt d).noShadow Tb Sb = true
  | .mk _ _ _ _ e, _, _, _, _, _, hS, hT => by
    simp only [Method.fr, Method.noShadow, Bool.and_eq_true]
    rw [dom_renBounds frs_length, names_renParams frs_length]
    exact ⟨⟨all_not_contains_of (fun X hX hm => hT X hm (frs_at hX)),
      all_not_contains_of (fun y hy hm => hS y hm (frs_at hy))⟩, Expr.fr_noShadow ht e (hS.methV ht) hT.meth⟩
theorem Method.frList_noShadow {LV : List VarName} {LT : List TVarName} (ht : List.Mem this LV) :
    forall (Ms : List Method) {rv : VRen} {rt : TRen} {d : Nat} {Tb : List TVarName} {Sb : List VarName},
    Below LV d Sb -> Below LT d Tb -> Method.noShadowList Tb Sb (Method.frList LV LT rv rt d Ms) = true
  | [], _, _, _, _, _, _, _ => rfl
  | M :: Ms, _, _, _, _, _, hS, hT => by
    simp only [Method.frList, Method.noShadowList, Bool.and_eq_true]
    exact ⟨Method.fr_noShadow ht M hS hT, Method.frList_noShadow ht Ms hS hT⟩
end

mutual
theorem Expr.fr_uniq {LV : List VarName} {LT : List TVarName} :
    forall (e : Expr) {rv : VRen} {rt : TRen} {d : Nat}, (e.fr LV LT rv rt d).uniq
  | .var _, _, _, _ => by simp only [Expr.fr, Expr.uniq]
  | .call e _ _ es, _, _, _ => ⟨Expr.fr_uniq e, Expr.frList_uniq es⟩
  | .superCall e _ _ _ es, _, _, _ => ⟨Expr.fr_uniq e, Expr.frList_uniq es⟩
  | .field e _, _, _, _ => Expr.fr_uniq e
  | .new _ _ es, _, _, _ => Expr.frList_uniq es
  | .newLocal _ _ _ _ es Ms, _, _, _ => ⟨Expr.frList_uniq es, Method.frList_uniq Ms⟩
  | .ifInst e0 _ _ e1 e2, _, _, _ => ⟨Expr.fr_uniq e0, Expr.fr_uniq e1, Expr.fr_uniq e2⟩
theorem Expr.frList_uniq {LV : List VarName} {LT : List TVarName} :
    forall (es : List Expr) {rv : VRen} {rt : TRen} {d : Nat}, Expr.uniqList (Expr.frList LV LT rv rt d es)
  | [], _, _, _ => by simp only [Expr.frList, Expr.uniqList]
  | e :: es, _, _, _ => ⟨Expr.fr_uniq e, Expr.frList_uniq es⟩
theorem Method.fr_uniq {LV : List VarName} {LT : List TVarName} :
    forall (M : Method) {rv : VRen} {rt : TRen} {d : Nat}, (M.fr LV LT rv rt d).uniq
  | .mk _ _ _ _ e, _, _, _ => by
    simp only [Method.fr, Method.uniq]
    rw [dom_renBounds frs_length, names_renParams frs_length]
    exact ⟨frs_nodup, frs_nodup, Expr.fr_uniq e⟩
theorem Method.frList_uniq {LV : List VarName} {LT : List TVarName} :
    forall (Ms : List Method) {rv : VRen} {rt : TRen} {d : Nat}, Method.uniqList (Method.frList LV LT rv rt d Ms)
  | [], _, _, _ => by simp only [Method.frList, Method.uniqList]
  | M :: Ms, _, _, _ => ⟨Method.fr_uniq M, Method.frList_uniq Ms⟩
end

mutual
theorem Expr.ifVars_vb : forall (e : Expr) {y : VarName}, List.Mem y e.ifVars -> List.Mem y e.vbinders
  | .var _, _, h => by simp [Expr.ifVars] at h
  | .call e _ _ es, _, h => by
    simp only [Expr.ifVars, Expr.vbinders, listMem_iff, List.mem_append] at h ⊢
    rcases h with h | h
    . exact Or.inl (Expr.ifVars_vb e h)
    . exact Or.inr (Expr.ifVarsList_vb es h)
  | .superCall e _ _ _ es, _, h => by
    simp only [Expr.ifVars, Expr.vbinders, listMem_iff, List.mem_append] at h ⊢
    rcases h with h | h
    . exact Or.inl (Expr.ifVars_vb e h)
    . exact Or.inr (Expr.ifVarsList_vb es h)
  | .field e _, _, h => by
    simp only [Expr.ifVars, Expr.vbinders] at h ⊢
    exact Expr.ifVars_vb e h
  | .new _ _ es, _, h => by
    simp only [Expr.ifVars, Expr.vbinders] at h ⊢
    exact Expr.ifVarsList_vb es h
  | .newLocal _ _ _ _ es Ms, _, h => by
    simp only [Expr.ifVars, Expr.vbinders, listMem_iff, List.mem_append] at h ⊢
    rcases h with h | h
    . exact Or.inl (Expr.ifVarsList_vb es h)
    . exact Or.inr (Method.ifVarsList_vb Ms h)
  | .ifInst e0 _ _ e1 e2, _, h => by
    simp only [Expr.ifVars, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons] at h ⊢
    rcases h with ((h | h) | h) | h
    . exact Or.inl (Or.inl (Or.inl h))
    . exact Or.inl (Or.inl (Or.inr (Expr.ifVars_vb e0 h)))
    . exact Or.inl (Or.inr (Expr.ifVars_vb e1 h))
    . exact Or.inr (Expr.ifVars_vb e2 h)
theorem Expr.ifVarsList_vb : forall (es : List Expr) {y : VarName},
    List.Mem y (Expr.ifVarsList es) -> List.Mem y (Expr.vbindersList es)
  | [], _, h => by simp [Expr.ifVarsList] at h
  | e :: es, _, h => by
    simp only [Expr.ifVarsList, Expr.vbindersList, listMem_iff, List.mem_append] at h ⊢
    rcases h with h | h
    . exact Or.inl (Expr.ifVars_vb e h)
    . exact Or.inr (Expr.ifVarsList_vb es h)
theorem Method.ifVars_vb : forall (M : Method) {y : VarName}, List.Mem y M.ifVars -> List.Mem y M.vbinders
  | .mk _ _ _ _ e, _, h => by
    simp only [Method.ifVars, Method.vbinders, listMem_iff, List.mem_append] at h ⊢
    exact Or.inr (Expr.ifVars_vb e h)
theorem Method.ifVarsList_vb : forall (Ms : List Method) {y : VarName},
    List.Mem y (Method.ifVarsList Ms) -> List.Mem y (Method.vbindersList Ms)
  | [], _, h => by simp [Method.ifVarsList] at h
  | M :: Ms, _, h => by
    simp only [Method.ifVarsList, Method.vbindersList, listMem_iff, List.mem_append] at h ⊢
    rcases h with h | h
    . exact Or.inl (Method.ifVars_vb M h)
    . exact Or.inr (Method.ifVarsList_vb Ms h)
end

theorem domF_ren {rt : TRen} : forall (Fs : List Funnel), domF (Fs.map (Funnel.ren rt)) = (domF Fs).map (rn rt)
  | [] => rfl
  | F :: Fs => by
    rw [List.map_cons, domF_cons, domF_cons (F := F), List.map_append, domF_ren Fs]
    cases F <;> rfl

theorem cod_renBounds {r : TRen} : forall {Delta : Bounds} {Xs : List TVarName}, Xs.length = Delta.length ->
    ((Delta.zip Xs).map fun p => ({ X := p.2, T := p.1.T.ren r } : Bound)).map Bound.T =
      (Delta.map Bound.T).map (Ty.ren r)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | b :: Delta, X :: Xs, h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [cod_renBounds (by simpa using h)]

theorem tys_renParams {r : TRen} : forall {ps : List VarDecl} {xs : List VarName}, xs.length = ps.length ->
    ((ps.zip xs).map fun p => ({ T := p.1.T.ren r, x := p.2 } : VarDecl)).map VarDecl.T =
      (ps.map VarDecl.T).map (Ty.ren r)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | p :: ps, x :: xs, h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [tys_renParams (by simpa using h)]

theorem meth_tys_ren {r : TRen} {Delta : Bounds} {Xs : List TVarName} {ps : List VarDecl} {xs : List VarName}
    {T0 : Ty} (hL : Xs.length = Delta.length) (hl : xs.length = ps.length) :
    (T0.ren r :: cod ((Delta.zip Xs).map fun p => ({ X := p.2, T := p.1.T.ren r } : Bound)) ++
      ((ps.zip xs).map fun p => ({ T := p.1.T.ren r, x := p.2 } : VarDecl)).map VarDecl.T) =
    Ty.renList r (T0 :: cod Delta ++ ps.map VarDecl.T) := by
  rw [Ty.renList_eq_map]
  simp only [cod]
  rw [cod_renBounds hL, tys_renParams hl]
  simp only [List.map_cons, List.map_append, List.cons_append]

theorem CompEnv.varsIn {rv1 rv2 rv3 : VRen} {rt1 rt2 rt3 : TRen} {Sa Sb Ta Tb}
    (env : CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb) {Ys : List TVarName}
    (h : Ys.all Ta.contains = true) : (Ys.map (rn rt1)).all Tb.contains = true := by
  rw [all_contains_iff] at h ⊢
  intro Y hY
  rcases List.mem_map.mp hY with ⟨X, hX, e⟩
  subst e
  exact (env.st X (h X hX)).1

theorem CompEnv.tysIn {rv1 rv2 rv3 : VRen} {rt1 rt2 rt3 : TRen} {Sa Sb Ta Tb}
    (env : CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb) {Ts : List Ty}
    (h : (Ty.ftvList Ts).all Ta.contains = true) : (Ty.ftvList (Ty.renList rt1 Ts)).all Tb.contains = true := by
  rw [Ty.ftvList_ren]
  exact env.varsIn h

theorem CompEnv.tyIn {rv1 rv2 rv3 : VRen} {rt1 rt2 rt3 : TRen} {Sa Sb Ta Tb}
    (env : CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb) {T : Ty}
    (h : T.ftv.all Ta.contains = true) : (T.ren rt1).ftv.all Tb.contains = true := by
  rw [Ty.ftv_ren]
  exact env.varsIn h

mutual
theorem RenE.inv {rv1 rt1 a b} : RenE rv1 rt1 a b -> forall {rv2 rt2 rv3 rt3 Sa Sb Ta Tb},
    CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb -> IdRen rv3 -> IdRen rt3 ->
    (List.Mem this Sa -> List.Mem this Sb) -> a.closed Ta Sa = true -> b.noShadow Tb Sb = true ->
    NoThis a -> NoThis b -> b.uniq -> (forall k, List.Mem k a.locals -> KQ k) ->
    RenE rv2 rt2 b a /\ b.closed Tb Sb = true /\ (forall k, List.Mem k b.locals -> KQ k)
  | .var (x := x), rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, _, hS, hc, _, _, _, _, _ => by
    simp only [Expr.closed] at hc
    have hx : List.Mem x Sa := by simpa using hc
    have e : rn rv2 (rn rv1 x) = x /\ List.Mem (rn rv1 x) Sb := by
      by_cases ht : x = this
      . subst ht
        rw [rn_this (fun p hp => (env.k1 p hp).1), rn_this env.k2]
        exact ⟨rfl, hS hx⟩
      . have r := env.sv x hx ht
        rw [r.2, rn_id h3]
        exact ⟨rfl, r.1⟩
    refine ⟨?_, ?_, ?_⟩
    . have := RenE.var (rv := rv2) (rt := rt2) (x := x.ren rv1)
      simp only [VarName.ren_eq] at this
      rw [e.1] at this
      exact this
    . simp only [Expr.closed, VarName.ren_eq]
      simpa using e.2
    . intro k hk
      simp [Expr.locals] at hk
  | .call (Ts := Ts) (m := m) h1 hs1, rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, h3t, hS, hc, hn, ha, hb, hu,
      hk => by
    simp only [Expr.closed, Bool.and_eq_true, Expr.noShadow] at hc hn
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Expr.uniq, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at hu hk
    have r1 := RenE.inv h1 env h3 h3t hS hc.1.1 hn.1 ha.1 hb.1 hu.1 hk.1
    have r2 := RenEs.inv hs1 env h3 h3t hS hc.2 hn.2 ha.2 hb.2 hu.2 hk.2
    refine ⟨?_, ?_, ?_⟩
    . have := RenE.call (m := m) (Ts := Ty.renList rt1 Ts) r1.1 r2.1
      rwa [env.tys hc.1.2, Ty.renList_idRen h3t] at this
    . simp only [Expr.closed, Bool.and_eq_true]
      exact ⟨⟨r1.2.1, env.tysIn hc.1.2⟩, r2.2.1⟩
    . simp only [Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and]
      exact ⟨r1.2.2, r2.2.2⟩
  | .superCall (T := T) (Ts := Ts) (m := m) h1 hs1, rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, h3t, hS, hc, hn,
      ha, hb, hu, hk => by
    simp only [Expr.closed, Ty.ftvList, List.all_append, Bool.and_eq_true, Expr.noShadow] at hc hn
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Expr.uniq, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at hu hk
    have r1 := RenE.inv h1 env h3 h3t hS hc.1.1 hn.1 ha.1 hb.1 hu.1 hk.1
    have r2 := RenEs.inv hs1 env h3 h3t hS hc.2 hn.2 ha.2 hb.2 hu.2 hk.2
    refine ⟨?_, ?_, ?_⟩
    . have := RenE.superCall (m := m) (T := T.ren rt1) (Ts := Ty.renList rt1 Ts) r1.1 r2.1
      rwa [env.tys hc.1.2.2, Ty.renList_idRen h3t, env.ty hc.1.2.1, Ty.ren_idRen h3t] at this
    . simp only [Expr.closed, Ty.ftvList, List.all_append, Bool.and_eq_true]
      exact ⟨⟨r1.2.1, env.tyIn hc.1.2.1, env.tysIn hc.1.2.2⟩, r2.2.1⟩
    . simp only [Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and]
      exact ⟨r1.2.2, r2.2.2⟩
  | .field (f := f) h1, rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, h3t, hS, hc, hn, ha, hb, hu, hk => by
    have r1 := RenE.inv h1 env h3 h3t hS hc hn ha hb hu hk
    exact ⟨RenE.field r1.1, r1.2.1, r1.2.2⟩
  | .new (C := C) (Ts := Ts) hs1, rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, h3t, hS, hc, hn, ha, hb, hu, hk => by
    simp only [Expr.closed, Bool.and_eq_true, Expr.noShadow] at hc hn
    simp only [NoThis, Expr.vbinders] at ha hb
    simp only [Expr.uniq, Expr.locals] at hu hk
    have r2 := RenEs.inv hs1 env h3 h3t hS hc.2 hn ha hb hu hk
    refine ⟨?_, ?_, r2.2.2⟩
    . have := RenE.new (C := C) (Ts := Ty.renList rt1 Ts) r2.1
      rwa [env.tys hc.1, Ty.renList_idRen h3t] at this
    . simp only [Expr.closed, Bool.and_eq_true]
      exact ⟨env.tysIn hc.1, r2.2.1⟩
  | .newLocal (C := C) (Fs := Fs) (C' := C') (Ts := Ts) (Ms := Ms) (Ms' := Ms') hs1 hm1, rv2, rt2, rv3, rt3, Sa, Sb,
      Ta, Tb, env, h3, h3t, hS, hc, hn, ha, hb, hu, hk => by
    simp only [Expr.closed, Bool.and_eq_true, List.all_append, Expr.noShadow] at hc hn
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Expr.uniq] at hu
    simp only [Expr.locals, listMem_iff, List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq] at hk
    have r1 := RenEs.inv hs1 env h3 h3t hS hc.1.2 hn.1 ha.1 hb.1 hu.1 hk.2.1
    have r2 := RenMs.inv hm1 env.filt h3 h3t hc.2 hn.2 ha.2 hb.2 hu.2 hk.2.2
    have hinv : forall X, List.Mem X (domF Fs) -> rn rt2 (rn rt1 X) = X := fun X hX => by
      rw [(env.st X (all_contains_iff.mp hc.1.1.1 X hX)).2, rn_id h3t]
    have hF : (Fs.map (Funnel.ren rt1)).map (Funnel.ren rt2) = Fs := by
      rw [Funnels.ren_comp (rt3 := rt3) (fun X hX => (env.st X (all_contains_iff.mp hc.1.1.1 X hX)).2)]
      exact Funnels.ren_id (fun X _ => rn_id h3t X)
    have hk1 : KQ' Ms Fs := hk.1
    unfold KQ' at hk1
    refine ⟨?_, ?_, ?_⟩
    . have := RenE.newLocal (C := C) (C' := C') (Fs := Fs.map (Funnel.ren rt1)) (Ts := Ty.renList rt1 Ts) r1.1 r2.1
      rwa [hF, env.tys hc.1.1.2, Ty.renList_idRen h3t] at this
    . simp only [Expr.closed, Bool.and_eq_true, List.all_append]
      refine ⟨⟨⟨?_, env.tysIn hc.1.1.2⟩, r1.2.1⟩,
        Method.closedList_mono r2.2.1 (fun _ h => h) (fun _ h => (List.mem_filter.mp h).1)⟩
      rw [domF_ren]
      exact env.varsIn hc.1.1.1
    . simp only [Expr.locals, listMem_iff, List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq]
      refine ⟨?_, r1.2.2, r2.2.2⟩
      show KQ' Ms' (Fs.map (Funnel.ren rt1))
      unfold KQ'
      refine ⟨by rw [RenMs.names hm1]; exact hk1.1, ?_, ?_⟩
      . rw [domF_ren]
        exact List.pairwise_map.mpr (List.Pairwise.imp_of_mem
          (fun hX hY hne e => hne ((hinv _ hX).symm.trans ((congrArg (rn rt2) e).trans (hinv _ hY)))) hk1.2.1)
      . intro M hM
        have hMu := uniqList_mem hM hu.2
        have hMt : Not (List.Mem this M.vbinders) := fun h => hb.2 (vbindersListM_mem hM h)
        cases M with
        | mk D T0 m ps body =>
          simp only [Method.uniq, Method.vbinders, listMem_iff, List.mem_append, not_or] at hMu hMt
          simp only [Method.params, Method.bounds]
          exact ⟨hMu.2.1, hMu.1, hMt.1⟩
  | .ifInst (T := T) (x := x) (y := y) h01 h11 h21, rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, h3t, hS, hc, hn,
      ha, hb, hu, hk => by
    simp only [Expr.closed, Bool.and_eq_true, Expr.noShadow, Bool.not_eq_true'] at hc hn
    simp only [NoThis, Expr.vbinders, listMem_iff, List.mem_append, List.mem_cons, not_or] at ha hb
    simp only [Expr.uniq, Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and] at hu hk
    have hyS : Not (List.Mem y Sb) := by
      have := hn.1.1.2
      simp at this
      exact this
    have hx : Not (x = this) := fun e => ha.1.1.1 e.symm
    have hS1 : List.Mem this (x :: Sa) -> List.Mem this (y :: Sb) := fun h =>
      List.Mem.tail _ (hS ((List.mem_cons.mp h).resolve_left (fun e => hx e.symm)))
    have r0 := RenE.inv h01 env h3 h3t hS hc.1.1.1 hn.1.1.1 ha.1.1.2 hb.1.1.2 hu.1 hk.1.1
    have r1 := RenE.inv h11 (env.ifExt hx (fun e => hb.1.1.1 e.symm) hyS) (IdRen.cons h3) h3t hS1 hc.1.2 hn.1.2
      ha.1.2 hb.1.2 hu.2.1 hk.1.2
    have r2 := RenE.inv h21 env h3 h3t hS hc.2 hn.2 ha.2 hb.2 hu.2.2 hk.2
    refine ⟨?_, ?_, ?_⟩
    . have := RenE.ifInst (T := T.ren rt1) r0.1 r1.1 r2.1
      rwa [env.ty hc.1.1.2, Ty.ren_idRen h3t] at this
    . simp only [Expr.closed, Bool.and_eq_true]
      exact ⟨⟨⟨r0.2.1, env.tyIn hc.1.1.2⟩, r1.2.1⟩, r2.2.1⟩
    . simp only [Expr.locals, listMem_iff, List.mem_append, or_imp, forall_and]
      exact ⟨⟨r0.2.2, r1.2.2⟩, r2.2.2⟩
theorem RenEs.inv {rv1 rt1 as bs} : RenEs rv1 rt1 as bs -> forall {rv2 rt2 rv3 rt3 Sa Sb Ta Tb},
    CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb -> IdRen rv3 -> IdRen rt3 ->
    (List.Mem this Sa -> List.Mem this Sb) -> Expr.closedList Ta Sa as = true ->
    Expr.noShadowList Tb Sb bs = true -> Not (List.Mem this (Expr.vbindersList as)) ->
    Not (List.Mem this (Expr.vbindersList bs)) -> Expr.uniqList bs ->
    (forall k, List.Mem k (Expr.localsList as) -> KQ k) ->
    RenEs rv2 rt2 bs as /\ Expr.closedList Tb Sb bs = true /\ (forall k, List.Mem k (Expr.localsList bs) -> KQ k)
  | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨RenEs.nil, rfl, fun k hk => by simp [Expr.localsList] at hk⟩
  | .cons h1 hs1, rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, h3t, hS, hc, hn, ha, hb, hu, hk => by
    simp only [Expr.closedList, Bool.and_eq_true, Expr.noShadowList] at hc hn
    simp only [Expr.vbindersList, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Expr.uniqList, Expr.localsList, listMem_iff, List.mem_append, or_imp, forall_and] at hu hk
    have r1 := RenE.inv h1 env h3 h3t hS hc.1 hn.1 ha.1 hb.1 hu.1 hk.1
    have r2 := RenEs.inv hs1 env h3 h3t hS hc.2 hn.2 ha.2 hb.2 hu.2 hk.2
    refine ⟨RenEs.cons r1.1 r2.1, ?_, ?_⟩
    . simp only [Expr.closedList, Bool.and_eq_true]
      exact ⟨r1.2.1, r2.2.1⟩
    . simp only [Expr.localsList, listMem_iff, List.mem_append, or_imp, forall_and]
      exact ⟨r1.2.2, r2.2.2⟩
theorem RenM.inv {rv1 rt1 Ma Mb} : RenM rv1 rt1 Ma Mb -> forall {rv2 rt2 rv3 rt3 Sa Sb Ta Tb},
    CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb -> IdRen rv3 -> IdRen rt3 -> Ma.closed Ta Sa = true ->
    Mb.noShadow Tb Sb = true -> NoThisM Ma -> NoThisM Mb -> Mb.uniq -> (forall k, List.Mem k Ma.locals -> KQ k) ->
    RenM rv2 rt2 Mb Ma /\ Mb.closed Tb Sb = true /\ (forall k, List.Mem k Mb.locals -> KQ k)
  | .mk (Delta := Da) (T0 := T0) (m := m) (ps := psa) (Xs' := Xs1) (xs' := xs1) hL1 hl1 h1,
      rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, h3t, hc, hn, ha, hb, hu, hk => by
    simp only [Method.closed, Bool.and_eq_true, Method.noShadow] at hc hn
    simp only [NoThisM, Method.vbinders, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Method.uniq, Method.locals] at hu hk
    rw [dom_renBounds hL1] at hn hu
    rw [names_renParams hl1] at hn hb hu
    have hla : (psa.map VarDecl.x).length = xs1.length := by simp [hl1]
    have hLa : (dom Da).length = Xs1.length := by simp [dom, hL1]
    have env' := env.methExt hla hla.symm hu.2.1 hLa hLa.symm hu.1 ha.1 hb.1 hn.1.2 hn.1.1
    have r := RenE.inv h1 env' (IdRen.zip_append h3 _) (IdRen.zip_append h3t _)
      (fun _ => List.mem_append_left _ (List.Mem.head _)) hc.2 hn.2 ha.2 hb.2 hu.2.2 hk
    have hall := all_contains_iff.mp hc.1
    have hT0 : T0.ftv.all (Ta ++ dom Da).contains = true :=
      all_contains_iff.mpr (fun X hX => hall X (List.mem_append_left _ hX))
    have hBc := fun (b : Bound) (hb' : List.Mem b Da) => env'.ty (T := b.T) (all_contains_iff.mpr (fun X hX =>
      hall X (List.mem_append_right _
        (by rw [List.append_eq, ftvList_append]; exact List.mem_append_left _ (ftvList_map_mem (f := Bound.T) hb' hX)))))
    have hPc := fun (p : VarDecl) (hp : List.Mem p psa) => env'.ty (T := p.T) (all_contains_iff.mpr (fun X hX =>
      hall X (List.mem_append_right _
        (by rw [List.append_eq, ftvList_append]; exact List.mem_append_right _ (ftvList_map_mem (f := VarDecl.T) hp hX)))))
    refine ⟨?_, ?_, ?_⟩
    . have hm := RenM.mk (rv := rv2) (rt := rt2)
        (Delta := (Da.zip Xs1).map fun p => ({ X := p.2, T := p.1.T.ren ((dom Da).zip Xs1 ++ rt1) } : Bound))
        (T0 := T0.ren ((dom Da).zip Xs1 ++ rt1)) (m := m)
        (ps := (psa.zip xs1).map fun p => ({ T := p.1.T.ren ((dom Da).zip Xs1 ++ rt1), x := p.2 } : VarDecl))
        (Xs' := dom Da) (xs' := psa.map VarDecl.x) (by simp [dom, hL1]) (by simp [hl1])
        (by rw [dom_renBounds hL1, names_renParams hl1]; exact r.1)
      rw [dom_renBounds hL1, env'.ty hT0, bounds_comp hL1 (by simp [dom]) hBc, params_comp hl1 (by simp) hPc] at hm
      simp only [Ty.ren_idRen (IdRen.zip_append h3t (dom Da))] at hm
      rwa [bounds_zip_dom, params_zip_names] at hm
    . simp only [Method.closed, Bool.and_eq_true]
      rw [dom_renBounds hL1, names_renParams hl1]
      refine ⟨?_, r.2.1⟩
      rw [meth_tys_ren hL1 hl1, Ty.ftvList_ren]
      exact env'.varsIn hc.1
    . simp only [Method.locals]
      exact r.2.2
theorem RenMs.inv {rv1 rt1 Mas Mbs} : RenMs rv1 rt1 Mas Mbs -> forall {rv2 rt2 rv3 rt3 Sa Sb Ta Tb},
    CompEnv rv1 rv2 rv3 rt1 rt2 rt3 Sa Sb Ta Tb -> IdRen rv3 -> IdRen rt3 ->
    Method.closedList Ta Sa Mas = true -> Method.noShadowList Tb Sb Mbs = true ->
    Not (List.Mem this (Method.vbindersList Mas)) -> Not (List.Mem this (Method.vbindersList Mbs)) ->
    Method.uniqList Mbs -> (forall k, List.Mem k (Method.localsList Mas) -> KQ k) ->
    RenMs rv2 rt2 Mbs Mas /\ Method.closedList Tb Sb Mbs = true /\
      (forall k, List.Mem k (Method.localsList Mbs) -> KQ k)
  | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨RenMs.nil, rfl, fun k hk => by simp [Method.localsList] at hk⟩
  | .cons h1 hs1, rv2, rt2, rv3, rt3, Sa, Sb, Ta, Tb, env, h3, h3t, hc, hn, ha, hb, hu, hk => by
    simp only [Method.closedList, Bool.and_eq_true, Method.noShadowList] at hc hn
    simp only [Method.vbindersList, listMem_iff, List.mem_append, not_or] at ha hb
    simp only [Method.uniqList, Method.localsList, listMem_iff, List.mem_append, or_imp, forall_and] at hu hk
    have r1 := RenM.inv h1 env h3 h3t hc.1 hn.1 ha.1 hb.1 hu.1 hk.1
    have r2 := RenMs.inv hs1 env h3 h3t hc.2 hn.2 ha.2 hb.2 hu.2 hk.2
    refine ⟨RenMs.cons r1.1 r2.1, ?_, ?_⟩
    . simp only [Method.closedList, Bool.and_eq_true]
      exact ⟨r1.2.1, r2.2.1⟩
    . simp only [Method.localsList, listMem_iff, List.mem_append, or_imp, forall_and]
      exact ⟨r1.2.2, r2.2.2⟩
end

theorem CompEnv.top (xs : List VarName) (Xs : List TVarName) : CompEnv [] [] [] [] [] [] xs xs Xs Xs :=
  ⟨fun _ hw _ => ⟨hw, rfl⟩, fun _ hX => ⟨hX, rfl⟩, (fun p hp => by cases hp), (fun p hp => by cases hp),
    (fun p hp => by cases hp)⟩

theorem not_at_of_mem {A : Type} [Nm A] {L : List A} {d : Nat} {y : A} (h : List.Mem y L) : Not (At L d y) :=
  fun ⟨k, _, e⟩ => fresh_not_mem L k (e ▸ h)

theorem fresh_avoid (e : Expr) (LV : List VarName) (LT : List TVarName) {Xs : List TVarName} {xs : List VarName}
    (hk : forall k, List.Mem k e.locals -> KQ k) (hc : e.closed Xs xs = true) (ht : NoThis e) :
    exists e', Fresh e e' /\ (forall y, List.Mem y e'.vbinders -> Not (List.Mem y LV)) /\
      (forall X, List.Mem X e'.tbinders -> Not (List.Mem X LT)) /\ (forall k, List.Mem k e'.locals -> KQ k) /\
      e'.noShadow Xs xs = true /\ Not (List.Mem this e'.ifVars) /\ e'.closed Xs xs = true := by
  have hthis : List.Mem this (this :: LV ++ xs) := List.mem_append_left _ (List.Mem.head _)
  have hvb : forall y, List.Mem y (e.fr (this :: LV ++ xs) (LT ++ Xs) [] [] 0).vbinders ->
      Not (List.Mem y (this :: LV ++ xs)) := fun y hy hm => not_at_of_mem hm (Expr.fr_vb e hy)
  have htb : forall Y, List.Mem Y (e.fr (this :: LV ++ xs) (LT ++ Xs) [] [] 0).tbinders ->
      Not (List.Mem Y (LT ++ Xs)) := fun Y hY hm => not_at_of_mem hm (Expr.fr_tb e hY)
  have hns := Expr.fr_noShadow hthis e (LT := LT ++ Xs) (rv := []) (rt := []) (d := 0) (Tb := Xs) (Sb := xs)
    (fun _ hy => not_at_of_mem (List.mem_append_right _ hy)) (fun _ hY => not_at_of_mem (List.mem_append_right _ hY))
  have hnt : NoThis (e.fr (this :: LV ++ xs) (LT ++ Xs) [] [] 0) := fun h => hvb this h hthis
  have r := RenE.inv (Expr.fr_ren e [] [] 0) (CompEnv.top xs Xs) (fun p hp => by cases hp)
    (fun p hp => by cases hp) id hc hns ht hnt (Expr.fr_uniq e) hk
  exact ⟨_, ⟨Expr.fr_ren e [] [] 0, r.1⟩, fun y hy hm => hvb y hy (List.mem_append_left _ (List.Mem.tail _ hm)),
    fun X hX hm => htb X hX (List.mem_append_left _ hm), r.2.2, hns, fun h => hnt (Expr.ifVars_vb _ h), r.2.1⟩

theorem freshM_avoid (M : Method) (LV : List VarName) (LT : List TVarName) {Xs : List TVarName} {xs : List VarName}
    (hk : forall k, List.Mem k M.locals -> KQ k) (hc : M.closed Xs xs = true) (ht : NoThisM M) :
    exists M', FreshM M M' /\ (forall y, List.Mem y M'.vbinders -> Not (List.Mem y LV)) /\
      (forall X, List.Mem X M'.tbinders -> Not (List.Mem X LT)) /\ (forall k, List.Mem k M'.locals -> KQ k) /\
      M'.noShadow Xs xs = true /\ Not (List.Mem this M'.ifVars) /\ M'.closed Xs xs = true /\ NoThisM M' /\
      M'.uniq := by
  have hthis : List.Mem this (this :: LV ++ xs) := List.mem_append_left _ (List.Mem.head _)
  have hvb : forall y, List.Mem y (M.fr (this :: LV ++ xs) (LT ++ Xs) [] [] 0).vbinders ->
      Not (List.Mem y (this :: LV ++ xs)) := fun y hy hm => not_at_of_mem hm (Method.fr_vb M hy)
  have htb : forall Y, List.Mem Y (M.fr (this :: LV ++ xs) (LT ++ Xs) [] [] 0).tbinders ->
      Not (List.Mem Y (LT ++ Xs)) := fun Y hY hm => not_at_of_mem hm (Method.fr_tb M hY)
  have hns := Method.fr_noShadow hthis M (LT := LT ++ Xs) (rv := []) (rt := []) (d := 0) (Tb := Xs) (Sb := xs)
    (fun _ hy => not_at_of_mem (List.mem_append_right _ hy)) (fun _ hY => not_at_of_mem (List.mem_append_right _ hY))
  have hnt : NoThisM (M.fr (this :: LV ++ xs) (LT ++ Xs) [] [] 0) := fun h => hvb this h hthis
  have r := RenM.inv (Method.fr_ren M [] [] 0) (CompEnv.top xs Xs) (fun p hp => by cases hp)
    (fun p hp => by cases hp) hc hns ht hnt (Method.fr_uniq M) hk
  exact ⟨_, ⟨Method.fr_ren M [] [] 0, r.1⟩, fun y hy hm => hvb y hy (List.mem_append_left _ (List.Mem.tail _ hm)),
    fun X hX hm => htb X hX (List.mem_append_left _ hm), r.2.2, hns, fun h => hnt (Method.ifVars_vb _ h), r.2.1,
    hnt, Method.fr_uniq M⟩

end Funnelling.High
