import Funnelling.Soundness

namespace Funnelling.Examples

open Funnelling.High

def cn (s : String) : ClassName := { name := s }
def mn (s : String) : MethName := { name := s }
def fn (s : String) : FieldName := { name := s }
def vn (s : String) : VarName := { name := s }
def tn (s : String) : TVarName := { name := s }

def obj : Ty := .cls Object []
def tA : Ty := .cls (cn "A") []
def tB : Ty := .cls (cn "B") []
def gA : GTy := .cls (cn "A") []
def gB : GTy := .cls (cn "B") []
def vA : Value := .new (cn "A") [] []
def vB : Value := .new (cn "B") [] []
def thisE : Expr := .var this

def decObject : Dec := { C := Object, bounds := [], C' := Object, Ts := [], Ms := [], Ss := [] }
def decA : Dec := { C := cn "A", bounds := [], C' := Object, Ts := [], Ms := [], Ss := [] }
def decB : Dec :=
  { C := cn "B", bounds := [], C' := Object, Ts := [], Ms := [.mk [] tB (mn "onlyB") [] vB], Ss := [] }
def decBox : Dec :=
  { C := cn "Box", bounds := [{ X := tn "X", T := obj }], C' := Object, Ts := [],
    Ms := [.mk [] (.var (tn "X")) (mn "get") [] (.field thisE (fn "val"))],
    Ss := [{ T := .var (tn "X"), f := fn "val" }] }
def decC1 : Dec :=
  { C := cn "C1", bounds := [], C' := Object, Ts := [], Ms := [.mk [] tA (mn "m") [] vA], Ss := [] }
def decC2 : Dec := { C := cn "C2", bounds := [], C' := cn "C1", Ts := [], Ms := [], Ss := [] }

def d1 : Decls := [decObject, decA, decB, decBox, decC1, decC2]

-- W1: the class table d1 is well formed.
theorem w1 : WFDecls d1 := by decide

-- W2: a method declaring two parameters named x violates A4.
def decDup : Dec :=
  { C := cn "Dup", bounds := [], C' := Object, Ts := [],
    Ms := [.mk [] tA (mn "m") [{ T := tA, x := vn "x" }, { T := tA, x := vn "x" }] (.var (vn "x"))],
    Ss := [] }
theorem w2 : Not (WFDecls [decObject, decA, decDup]) := by decide

-- W3: an if binding the parameter x again violates A7.
def decShadow : Dec :=
  { C := cn "Shadow", bounds := [], C' := Object, Ts := [],
    Ms := [.mk [] tA (mn "m") [{ T := tA, x := vn "x" }]
      (.ifInst (.var (vn "x")) tA (vn "x") (.var (vn "x")) (.var (vn "x")))],
    Ss := [] }
theorem w3 : Not (WFDecls [decObject, decA, decShadow]) := by decide

-- W4: a superclass that is not declared violates A9 and A10.
def decOrphan : Dec := { C := cn "Orphan", bounds := [], C' := cn "Missing", Ts := [], Ms := [], Ss := [] }
theorem w4 : Not (WFDecls [decObject, decOrphan]) := by decide

-- R1: rule simpleFieldFound.
theorem r1 : Reduces d1 (.field (Value.new (cn "Box") [gA] [vA]) (fn "val")) vA :=
  And.intro
    (Step.simpleFieldFound (D := decBox) (vs1 := [vA]) (vs := [])
      (.dec (.tail _ (.tail _ (.tail _ (.head _))))) rfl (.head _))
    (by decide)

-- R2: rule simpleAddSuper.
theorem r2 : Reduces d1 (.call (Value.new (cn "C2") [] []) [] (mn "m") [])
    (.superCall (Value.new (cn "C2") [] []) (.cls (cn "C2") []) [] (mn "m") []) :=
  And.intro (Step.simpleAddSuper (Gs' := []) (vs := []) rfl) (by decide)

-- R3: rule searchSuper.
theorem r3 : Reduces d1 (.superCall (Value.new (cn "C2") [] []) (.cls (cn "C2") []) [] (mn "m") [])
    (.superCall (Value.new (cn "C2") [] []) (.cls (cn "C1") []) [] (mn "m") []) :=
  And.intro
    (Step.searchSuper (D := decC2) (Gs := []) (Gs' := []) (vs := [])
      (.dec (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (by intro h; cases h)
      (by decide) rfl)
    (by decide)

-- R4: rule simpleFound, with no names to rename.
theorem r4 : Reduces d1 (.superCall (Value.new (cn "C2") [] []) (.cls (cn "C1") []) [] (mn "m") []) vA :=
  And.intro
    (Step.simpleFound (D := decC1) (M := .mk [] tA (mn "m") [] vA) (Gs := []) (Gs' := []) (vs := [])
      (Delta' := []) (T0 := tA) (ps := []) (e0 := vA)
      (.dec (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _)
      (And.intro (.mk (Xs' := []) (xs' := []) rfl rfl (.new .nil)) (by decide)) rfl rfl rfl)
    (by decide)

-- R5: rule ctx, inside the receiver of a call.
theorem r5 : Reduces d1 (.call (.field (Value.new (cn "Box") [gA] [vA]) (fn "val")) [] (mn "m") [])
    (.call vA [] (mn "m") []) :=
  And.intro
    (Step.ctx (E := .callRecv .hole [] (mn "m") [])
      (Step.simpleFieldFound (D := decBox) (vs1 := [vA]) (vs := [])
        (.dec (.tail _ (.tail _ (.tail _ (.head _))))) rfl (.head _)))
    (by decide)

-- R6: rules ifThen and ifElse.
theorem r6Then : Reduces d1 (.ifInst vA tA (vn "x") (.var (vn "x")) vB) vA :=
  And.intro
    (Step.ifThen (v := vA) (C' := cn "A") (Ts := []) (Ts' := []) (x := vn "x") (e1 := .var (vn "x"))
      (e1' := .var (vn "x")) (e2 := vB) .refl (And.intro .var (by decide)))
    (by decide)

theorem r6Else : Reduces d1 (.ifInst vA tB (vn "x") (.var (vn "x")) vB) vB := by
  sorry

-- R11: three steps, new C2<>().m() reduces to new A<>().
theorem r11 : Steps d1 (.call (Value.new (cn "C2") [] []) [] (mn "m") []) vA :=
  Steps.step r2 (Steps.step r3 (Steps.step r4 Steps.refl))

def tFoo (T : Ty) : Ty := .cls (cn "Foo") [T]
def decFoo : Dec :=
  { C := cn "Foo", bounds := [{ X := tn "X", T := obj }], C' := Object, Ts := [],
    Ms := [.mk [] (.var (tn "X")) (mn "x") [] (.call thisE [] (mn "x") [])], Ss := [] }
def myFooMethod : Method := .mk [] (.var (tn "Y")) (mn "x") [] (.var (vn "y"))
def myFooBody : Expr := .newLocal (cn "MyFoo") [.funnel (tn "Y")] (cn "Foo") [.var (tn "Y")] [] [myFooMethod]
def mkMethod : Method :=
  .mk [{ X := tn "Y", T := obj }] (tFoo (.var (tn "Y"))) (mn "mk") [{ T := .var (tn "Y"), x := vn "y" }] myFooBody
def decMaker : Dec := { C := cn "Maker", bounds := [], C' := Object, Ts := [], Ms := [mkMethod], Ss := [] }

def d2 : Decls := [decObject, decA, decB, decFoo, decMaker]

-- W5: the class table d2, with the funnelled local class MyFoo, is well formed.
theorem w5 : WFDecls d2 := by decide

def vLocal : Value := .newLocal (cn "MyFoo") [gA] (cn "Foo") [gA] [] [.mk [] tA (mn "x") [] vA]

-- R7: rule simpleFound renames Y and y into Y1 and y1, then replaces Y1 and y1.
theorem r7 : Reduces d2
    (.superCall (Value.new (cn "Maker") [] []) (.cls (cn "Maker") []) [tA] (mn "mk") [vA]) vLocal :=
  And.intro
    (Step.simpleFound (D := decMaker) (M := mkMethod) (Gs := []) (Gs' := [gA]) (vs := [vA])
      (Delta' := [{ X := tn "Y1", T := obj }]) (T0 := tFoo (.var (tn "Y1")))
      (ps := [{ T := .var (tn "Y1"), x := vn "y1" }])
      (e0 := .newLocal (cn "MyFoo") [.funnel (tn "Y1")] (cn "Foo") [.var (tn "Y1")] []
        [.mk [] (.var (tn "Y1")) (mn "x") [] (.var (vn "y1"))])
      (.dec (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.head _)
      (And.intro
        (.mk (Xs' := [tn "Y1"]) (xs' := [vn "y1"]) rfl rfl
          (.newLocal .nil (.cons (.mk (Xs' := []) (xs' := []) rfl rfl .var) .nil)))
        (by decide))
      rfl rfl rfl)
    (by decide)

-- R8: rule innerFound.
theorem r8 : Reduces d2 (.call vLocal [] (mn "x") []) vA :=
  And.intro
    (Step.innerFound (v0 := vLocal) (M := .mk [] tA (mn "x") [] vA) (Gs' := []) (vs := [])
      (Delta' := []) (T0 := tA) (ps := []) (e0 := vA) rfl (.head _)
      (And.intro (.mk (Xs' := []) (xs' := []) rfl rfl (.new .nil)) (by decide)) rfl rfl rfl)
    (by decide)

-- R9: rule innerSuper.
theorem r9 : Reduces d2 (.call vLocal [] (mn "other") [])
    (.superCall vLocal (tFoo tA) [] (mn "other") []) :=
  And.intro
    (Step.innerSuper (v0 := vLocal) (Gs' := []) (vs := []) rfl (by decide))
    (by decide)

-- R10: rule innerFieldSuper.
theorem r10 : Reduces d2 (.field vLocal (fn "f")) (.field (Value.new (cn "Foo") [gA] []) (fn "f")) :=
  And.intro Step.innerFieldSuper (by decide)

-- T1: new Box<A<>>(new A<>()).val has type A<>.
theorem kindA : Kind d1 [] tA :=
  Kind.cls (Delta0 := []) (Ts0 := []) (Scope.dec (D := decA) (.dec (.tail _ (.head _))))
    (by intro T h; cases h) rfl .nil

theorem subAObj : Sub d1 [] tA obj :=
  Sub.inherit (D := decA) (.dec (.tail _ (.head _))) rfl .refl

theorem kindBoxA : Kind d1 [] (.cls (cn "Box") [tA]) :=
  Kind.cls (Delta0 := decBox.bounds) (Ts0 := [tA])
    (Scope.dec (D := decBox) (.dec (.tail _ (.tail _ (.tail _ (.head _))))))
    (by intro T h; cases h with
      | head => exact kindA
      | tail _ h => cases h)
    rfl (.cons subAObj .nil)

theorem typA : Typing d1 .funnelled [] [] vA tA :=
  Typing.newTop (D := decA) (es1 := []) (es2 := []) (.dec (.tail _ (.head _))) kindA rfl .nil
    Typing.newObject

theorem typBox : Typing d1 .funnelled [] [] (Value.new (cn "Box") [gA] [vA]) (.cls (cn "Box") [tA]) :=
  Typing.newTop (D := decBox) (es1 := [vA]) (es2 := [])
    (.dec (.tail _ (.tail _ (.tail _ (.head _))))) kindBoxA rfl (.cons typA .nil) Typing.newObject

theorem t1 : Typing d1 .funnelled [] [] (.field (Value.new (cn "Box") [gA] [vA]) (fn "val")) tA :=
  Typing.declField (D := decBox) (T := .var (tn "X")) typBox
    (.dec (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) rfl

-- T2: new Box<A<>>(new B<>()) is ill typed: B<> is not a subtype of A<>.
theorem t2 : Not (Typing d1 .funnelled [] [] (Value.new (cn "Box") [gA] [vB]) (.cls (cn "Box") [tA])) := by
  sorry

def myFooK : K := .loc (cn "MyFoo") [.funnel (tn "Y")] (cn "Foo") [.var (tn "Y")] [] [myFooMethod]

theorem myFooDeclared : Declared d2 myFooK :=
  Declared.loc (k := .dec decMaker) (.dec (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    (.head _) (Exists.intro .hole rfl)

-- C1: rule cast-down accepts the type test instanceof MyFoo<X> from Foo<X>.
theorem c1 : Cast d2 [{ X := tn "X", T := obj }] (tFoo (.var (tn "X"))) (.cls (cn "MyFoo") [.var (tn "X")]) :=
  Cast.down (Xs := [tn "Y"]) (Ts' := [.var (tn "Y")])
    (Sub.inheritLocal myFooDeclared rfl .refl)
    (Generic.loc myFooDeclared)
    (Sub.inheritLocal myFooDeclared rfl .refl)
    (by intro X h; cases h with
      | head => exact .head _
      | tail _ h => cases h)

-- C2: rule cast-down rejects the type test instanceof MyFoo<X> from Object<>.
theorem c2 : Not (Cast d2 [{ X := tn "X", T := obj }] obj (.cls (cn "MyFoo") [.var (tn "X")])) := by
  sorry

-- M1: the class Maker is Ok under funnelled typing.
theorem m1 : ClassOk d2 .funnelled decMaker := by
  sorry

def brokenBody : Expr :=
  .ifInst (.var (vn "other")) (.cls (cn "MyFoo") []) (vn "w") (.var (vn "w"))
    (.newLocal (cn "MyFoo") [] (cn "Foo") [.var (tn "X")] [] [.mk [] (.var (tn "X")) (mn "x") [] (.var (vn "x"))])
def decBroken : Dec :=
  { C := cn "Broken", bounds := [], C' := Object, Ts := [],
    Ms := [.mk [{ X := tn "X", T := obj }] (tFoo (.var (tn "X"))) (mn "m")
      [{ T := obj, x := vn "other" }, { T := .var (tn "X"), x := vn "x" }] brokenBody],
    Ss := [] }

def d3 : Decls := [decObject, decA, decB, decFoo, decBroken]

def eA : Expr := .call (Value.new (cn "Broken") [] []) [tA] (mn "m") [Value.new (cn "Foo") [gA] [], vA]
def brokenMain : Expr :=
  .call (.call (.call (Value.new (cn "Broken") [] []) [tB] (mn "m") [eA, vB]) [] (mn "x") []) [] (mn "onlyB") []

def Stuck (d : Decls) (e : Expr) : Prop := Not (IsValue e) /\ forall e', Not (Reduces d e e')

-- W6: Example 1 in the core language is well formed.
theorem w6 : WFDecls d3 /\ WFExpr brokenMain := by decide

-- J1: Example 1 is well typed under Java typing (rule new-local-java).
theorem j1 : ProgOk d3 .java brokenMain := by
  sorry

-- J2: Example 1 reduces to new A<>().onlyB(), which is stuck.
theorem j2 : Steps d3 brokenMain (.call vA [] (mn "onlyB") []) /\ Stuck d3 (.call vA [] (mn "onlyB") []) := by
  sorry

-- N1: Example 1 is ill typed under funnelled typing.
theorem n1 : Not (ProgOk d3 .funnelled brokenMain) := by
  sorry

def decLeaker : Dec :=
  { C := cn "Leaker", bounds := [], C' := Object, Ts := [],
    Ms := [
      .mk [{ X := tn "Y", T := obj }] (.cls (cn "MyFoo2") []) (mn "mk2") [{ T := .var (tn "Y"), x := vn "y" }]
        (.newLocal (cn "MyFoo2") [] (cn "Foo") [.var (tn "Y")] [] [.mk [] (.var (tn "Y")) (mn "x") [] (.var (vn "y"))]),
      .mk [{ X := tn "Y", T := obj }] (tFoo (.var (tn "Y"))) (mn "leak") [{ T := .cls (cn "MyFoo2") [], x := vn "z" }]
        (.var (vn "z"))],
    Ss := [] }

def d4 : Decls := [decObject, decA, decB, decFoo, decLeaker]

-- W7: the class table d4 is well formed.
theorem w7 : WFDecls d4 := by decide

-- L1: the class Leaker is Ok under Java typing.
theorem l1 : ClassOk d4 .java decLeaker := by
  sorry

-- L2: the class Leaker is not Ok under funnelled typing.
theorem l2 : Not (ClassOk d4 .funnelled decLeaker) := by
  sorry

end Funnelling.Examples
