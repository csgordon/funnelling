import Funnelling.Sound.GSubstRen

open Funnelling.SoundSimp

namespace Funnelling

inductive BaseStep (d : Decls) : Expr -> Expr -> Prop
  | simpleFieldFound {D f} {Gs : List GTy} {vs1 vs : List Value} {v : Value} :
      Declared d (.dec D) ->
      vs1.length = D.Ss.length ->
      List.Mem (f, v) ((D.Ss.map Slot.f).zip vs1) ->
      BaseStep d (.field (Value.new D.C Gs (vs1 ++ vs)) f) v
  | simpleFieldSuper {D f} {Gs : List GTy} {vs1 vs : List Value} :
      Declared d (.dec D) ->
      vs1.length = D.Ss.length ->
      Not (List.Mem f (D.Ss.map Slot.f)) ->
      Not (D.C = Object) ->
      Gs.length = D.bounds.length ->
      BaseStep d (.field (Value.new D.C Gs (vs1 ++ vs)) f)
        (.field (.new D.C' (Ty.substList (bind D.bounds (Gs : List Ty)) D.Ts) vs) f)
  | innerFieldSuper {C C' Ms f} {Gs Gs' : List GTy} {vs : List Value} :
      BaseStep d (.field (Value.newLocal C Gs C' Gs' vs Ms) f) (.field (Value.new C' Gs' vs) f)
  | ifThen {C' Ts Ts' x e1 e1' e2} {v : Value} :
      Sub d [] (typeOf v) (.cls C' Ts') ->
      Fresh e1 e1' ->
      VSubstDefined [x] e1' ->
      BaseStep d (.ifInst v (.cls C' Ts) x e1 e2) (e1'.vsubst [(x, v)])
  | ifElse {C' Ts x e1 e2} {v : Value} :
      Not (exists Ts', Sub d [] (typeOf v) (.cls C' Ts')) ->
      BaseStep d (.ifInst v (.cls C' Ts) x e1 e2) e2
  | simpleAddSuper {C m} {v : Value} {Gs Gs' : List GTy} {vs0 vs : List Value} :
      v = Value.new C Gs vs0 ->
      BaseStep d (.call v Gs' m vs) (.superCall v (.cls C Gs) Gs' m vs)
  | simpleFound {D M m Delta' T0 ps e0 e} {v0 : Value} {Gs Gs' : List GTy} {vs : List Value} :
      Declared d (.dec D) ->
      List.Mem M D.Ms ->
      FreshM M (.mk Delta' T0 m ps e0) ->
      Gs.length = D.bounds.length -> Gs'.length = Delta'.length ->
      (dom D.bounds ++ dom Delta').Nodup ->
      (this :: ps.map VarDecl.x).Nodup ->
      ps.length = vs.length ->
      GSubstDefined (dom D.bounds ++ dom Delta') e0 ->
      VSubstDefined (this :: ps.map VarDecl.x) e0 ->
      e = (e0.gsubst (bind (D.bounds ++ Delta') (Gs ++ Gs'))).vsubst
        ((this :: ps.map VarDecl.x).zip (v0 :: vs)) ->
      BaseStep d (.superCall v0 (.cls D.C Gs) Gs' m vs) e
  | innerFound {C C' Ms M m Delta' T0 ps e0 e} {v0 : Value} {Gs Gs'' Gs' : List GTy} {vs0 vs : List Value} :
      v0 = Value.newLocal C Gs C' Gs'' vs0 Ms ->
      List.Mem M Ms ->
      FreshM M (.mk Delta' T0 m ps e0) ->
      Gs'.length = Delta'.length ->
      ps.length = vs.length ->
      (dom Delta').Nodup ->
      (this :: ps.map VarDecl.x).Nodup ->
      GSubstDefined (dom Delta') e0 ->
      VSubstDefined (this :: ps.map VarDecl.x) e0 ->
      e = (e0.gsubst (bind Delta' Gs')).vsubst ((this :: ps.map VarDecl.x).zip (v0 :: vs)) ->
      BaseStep d (.call v0 Gs' m vs) e
  | innerSuper {C C' Ms m} {v0 : Value} {Gs0 Gs Gs' : List GTy} {vs0 vs : List Value} :
      v0 = Value.newLocal C Gs0 C' Gs vs0 Ms ->
      Not (List.Mem m (Ms.map Method.name)) ->
      BaseStep d (.call v0 Gs' m vs) (.superCall v0 (.cls C' Gs) Gs' m vs)
  | searchSuper {D m} {v : Value} {Gs Gs' : List GTy} {vs : List Value} :
      Declared d (.dec D) ->
      Not (List.Mem m (D.Ms.map Method.name)) ->
      Not (D.C = Object) ->
      Gs.length = D.bounds.length ->
      BaseStep d (.superCall v (.cls D.C Gs) Gs' m vs)
        (.superCall v (.cls D.C' (Ty.substList (bind D.bounds (Gs : List Ty)) D.Ts)) Gs' m vs)

theorem BaseStep.toStep {d : Decls} {e e' : Expr} (h : BaseStep d e e') : Step d e e' := by
  cases h with
  | simpleFieldFound h1 h2 h3 => exact Step.simpleFieldFound h1 h2 h3
  | simpleFieldSuper h1 h2 h3 h4 h5 => exact Step.simpleFieldSuper h1 h2 h3 h4 h5
  | innerFieldSuper => exact Step.innerFieldSuper
  | ifThen h1 h2 h3 => exact Step.ifThen h1 h2 h3
  | ifElse h1 => exact Step.ifElse h1
  | simpleAddSuper h1 => exact Step.simpleAddSuper h1
  | simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => exact Step.simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact Step.innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | innerSuper h1 h2 => exact Step.innerSuper h1 h2
  | searchSuper h1 h2 h3 h4 => exact Step.searchSuper h1 h2 h3 h4

theorem BaseStep.nonhole {d : Decls} {e e' : Expr} (h : BaseStep d e e') {E : ECtx} {c : Expr}
    (hE : E.plug c = e) (hne : Not (E = .hole)) (hc : NonValue c) : False := by
  cases h with
  | simpleFieldFound => exact redex_field hc hE.symm hne
  | simpleFieldSuper => exact redex_field hc hE.symm hne
  | innerFieldSuper => exact redex_field hc hE.symm hne
  | ifThen => exact redex_if hc hE.symm hne
  | ifElse => exact redex_if hc hE.symm hne
  | simpleAddSuper => exact redex_call hc hE.symm hne
  | simpleFound => exact redex_super hc hE.symm hne
  | innerFound => exact redex_call hc hE.symm hne
  | innerSuper => exact redex_call hc hE.symm hne
  | searchSuper => exact redex_super hc hE.symm hne

theorem Step.strip {d : Decls} {a b2 : Expr} (h2 : Step d a b2) :
    forall {b1 : Expr}, BaseStep d a b1 -> BaseStep d a b2 := by
  induction h2 with
  | simpleFieldFound h1 h2 h3 => intro _ _; exact BaseStep.simpleFieldFound h1 h2 h3
  | simpleFieldSuper h1 h2 h3 h4 h5 => intro _ _; exact BaseStep.simpleFieldSuper h1 h2 h3 h4 h5
  | innerFieldSuper => intro _ _; exact BaseStep.innerFieldSuper
  | ifThen h1 h2 h3 => intro _ _; exact BaseStep.ifThen h1 h2 h3
  | ifElse h1 => intro _ _; exact BaseStep.ifElse h1
  | simpleAddSuper h1 => intro _ _; exact BaseStep.simpleAddSuper h1
  | simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    intro _ _; exact BaseStep.simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    intro _ _; exact BaseStep.innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | innerSuper h1 h2 => intro _ _; exact BaseStep.innerSuper h1 h2
  | searchSuper h1 h2 h3 h4 => intro _ _; exact BaseStep.searchSuper h1 h2 h3 h4
  | @ctx E c c2 hc ih =>
    intro b1 hb
    cases E with
    | hole => exact ih hb
    | _ => exact absurd (hb.nonhole rfl (by simp) (Step.not_value hc)) id

def ECtx.comp : ECtx -> ECtx -> ECtx
  | .hole, E' => E'
  | .callRecv E Gs m es, E' => .callRecv (E.comp E') Gs m es
  | .callArg v Gs m vs E es, E' => .callArg v Gs m vs (E.comp E') es
  | .superRecv E G Gs m es, E' => .superRecv (E.comp E') G Gs m es
  | .superArg v G Gs m vs E es, E' => .superArg v G Gs m vs (E.comp E') es
  | .field E f, E' => .field (E.comp E') f
  | .newArg C Gs vs E es, E' => .newArg C Gs vs (E.comp E') es
  | .localArg C Gs C' Gs' vs E es Ms, E' => .localArg C Gs C' Gs' vs (E.comp E') es Ms
  | .ifCond E G x e1 e2, E' => .ifCond (E.comp E') G x e1 e2

theorem ECtx.comp_plug : forall (E E' : ECtx) (a : Expr), (E.comp E').plug a = E.plug (E'.plug a)
  | .hole, _, _ => rfl
  | .callRecv E _ _ _, E', a => by simp only [ECtx.comp, ECtx.plug, ECtx.comp_plug E E' a]
  | .callArg _ _ _ _ E _, E', a => by simp only [ECtx.comp, ECtx.plug, ECtx.comp_plug E E' a]
  | .superRecv E _ _ _ _, E', a => by simp only [ECtx.comp, ECtx.plug, ECtx.comp_plug E E' a]
  | .superArg _ _ _ _ _ E _, E', a => by simp only [ECtx.comp, ECtx.plug, ECtx.comp_plug E E' a]
  | .field E _, E', a => by simp only [ECtx.comp, ECtx.plug, ECtx.comp_plug E E' a]
  | .newArg _ _ _ E _, E', a => by simp only [ECtx.comp, ECtx.plug, ECtx.comp_plug E E' a]
  | .localArg _ _ _ _ _ E _ _, E', a => by simp only [ECtx.comp, ECtx.plug, ECtx.comp_plug E E' a]
  | .ifCond E _ _ _ _, E', a => by simp only [ECtx.comp, ECtx.plug, ECtx.comp_plug E E' a]

theorem Step.toBase {d : Decls} {e e' : Expr} (h : Step d e e') :
    exists (E : ECtx) (a a' : Expr), e = E.plug a /\ e' = E.plug a' /\ BaseStep d a a' := by
  induction h with
  | simpleFieldFound h1 h2 h3 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.simpleFieldFound h1 h2 h3)))))
  | simpleFieldSuper h1 h2 h3 h4 h5 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.simpleFieldSuper h1 h2 h3 h4 h5)))))
  | innerFieldSuper =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl BaseStep.innerFieldSuper))))
  | ifThen h1 h2 h3 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.ifThen h1 h2 h3)))))
  | ifElse h1 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.ifElse h1)))))
  | simpleAddSuper h1 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.simpleAddSuper h1)))))
  | simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl
      (BaseStep.simpleFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)))))
  | innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl
      (BaseStep.innerFound h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)))))
  | innerSuper h1 h2 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.innerSuper h1 h2)))))
  | searchSuper h1 h2 h3 h4 =>
    exact Exists.intro ECtx.hole (Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl (BaseStep.searchSuper h1 h2 h3 h4)))))
  | @ctx E c c2 _ ih =>
    rcases ih with ⟨E', h'⟩
    rcases h' with ⟨a, h'⟩
    rcases h' with ⟨a', h'⟩
    refine Exists.intro (E.comp E') (Exists.intro a (Exists.intro a' (And.intro ?_ (And.intro ?_ h'.2.2))))
    . rw [ECtx.comp_plug, h'.1]
    . rw [ECtx.comp_plug, h'.2.1]

end Funnelling