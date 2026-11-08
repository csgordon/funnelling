import Funnelling.Sound.Ren

open Funnelling.SoundSimp

namespace Funnelling

mutual
def Expr.uniq : Expr -> Prop
  | .var _ => True
  | .call e _ _ es => e.uniq /\ Expr.uniqList es
  | .superCall e _ _ _ es => e.uniq /\ Expr.uniqList es
  | .field e _ => e.uniq
  | .new _ _ es => Expr.uniqList es
  | .newLocal _ _ _ _ es Ms => Expr.uniqList es /\ Method.uniqList Ms
  | .ifInst e0 _ _ e1 e2 => e0.uniq /\ e1.uniq /\ e2.uniq
def Expr.uniqList : List Expr -> Prop
  | [] => True
  | e :: es => e.uniq /\ Expr.uniqList es
def Method.uniq : Method -> Prop
  | .mk Delta _ _ ps e => (dom Delta).Nodup /\ (ps.map VarDecl.x).Nodup /\ e.uniq
def Method.uniqList : List Method -> Prop
  | [] => True
  | M :: Ms => M.uniq /\ Method.uniqList Ms
end

abbrev NoThis (e : Expr) : Prop := Not (List.Mem this e.vbinders)

abbrev NoThisM (M : Method) : Prop := Not (List.Mem this M.vbinders)

theorem rn_this {rv : VRen} (h : forall p, List.Mem p rv -> Not (p.1 = this)) : rn rv this = this := by
  simp only [rn]
  rw [lookup_none (fun p hp e => h p hp e)]
  rfl

theorem rn_ne_this {rv : VRen} (h : forall p, List.Mem p rv -> Not (p.2 = this)) {w : VarName}
    (hw : Not (w = this)) : Not (rn rv w = this) := by
  simp only [rn]
  cases hl : List.lookup w rv with
  | none => exact hw
  | some y => exact h (w, y) (lookup_mem hl)

end Funnelling
