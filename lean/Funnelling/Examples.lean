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
      (And.intro (.mk (Xs' := []) (xs' := []) rfl rfl (.new .nil)) (.mk (Xs' := []) (xs' := []) rfl rfl (.new .nil))) rfl rfl (by decide) (by decide) rfl (by decide) (by decide) rfl)
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
      (e1' := .var (vn "x")) (e2 := vB) .subRefl (And.intro .var .var) (by decide))
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
        (.mk (Xs' := [tn "Y"]) (xs' := [vn "y"]) rfl rfl
          (.newLocal .nil (.cons (.mk (Xs' := []) (xs' := []) rfl rfl .var) .nil))))
      rfl rfl (by decide) (by decide) rfl (by decide) (by decide) rfl)
    (by decide)

-- R8: rule innerFound.
theorem r8 : Reduces d2 (.call vLocal [] (mn "x") []) vA :=
  And.intro
    (Step.innerFound (v0 := vLocal) (M := .mk [] tA (mn "x") [] vA) (Gs' := []) (vs := [])
      (Delta' := []) (T0 := tA) (ps := []) (e0 := vA) rfl (.head _)
      (And.intro (.mk (Xs' := []) (xs' := []) rfl rfl (.new .nil)) (.mk (Xs' := []) (xs' := []) rfl rfl (.new .nil))) rfl rfl (by decide) (by decide) (by decide) (by decide) rfl)
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
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decA) (.dec (.tail _ (.head _))))
    (by intro T h; cases h) rfl .nil

theorem subAObj : Sub d1 [] tA obj :=
  Sub.subInherit (D := decA) (.dec (.tail _ (.head _))) rfl .subRefl

theorem kindBoxA : Kind d1 [] (.cls (cn "Box") [tA]) :=
  Kind.wfClass (Delta0 := decBox.bounds) (Ts0 := [tA])
    (Scope.dec (D := decBox) (.dec (.tail _ (.tail _ (.tail _ (.head _))))))
    (by intro T h; cases h with
      | head => exact kindA
      | tail _ h => cases h)
    rfl (.cons subAObj .nil)

theorem typA : Typing d1 [] [] vA tA :=
  Typing.newTop (D := decA) (es1 := []) (es2 := []) (.dec (.tail _ (.head _))) kindA rfl .nil
    Typing.newObject

theorem typBox : Typing d1 [] [] (Value.new (cn "Box") [gA] [vA]) (.cls (cn "Box") [tA]) :=
  Typing.newTop (D := decBox) (es1 := [vA]) (es2 := [])
    (.dec (.tail _ (.tail _ (.tail _ (.head _))))) kindBoxA rfl (.cons typA .nil) Typing.newObject

theorem t1 : Typing d1 [] [] (.field (Value.new (cn "Box") [gA] [vA]) (fn "val")) tA :=
  Typing.declField (D := decBox) (T := .var (tn "X")) typBox
    (.dec (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) rfl

-- T2: new Box<A<>>(new B<>()) is ill typed: B<> is not a subtype of A<>.
theorem t2 : Not (Typing d1 [] [] (Value.new (cn "Box") [gA] [vB]) (.cls (cn "Box") [tA])) := by
  sorry

def myFooK : K := .loc (cn "MyFoo") [.funnel (tn "Y")] (cn "Foo") [.var (tn "Y")] [] [myFooMethod]

theorem myFooDeclared : Declared d2 myFooK :=
  Declared.loc (k := .dec decMaker) (.dec (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    (.head _) (Exists.intro .hole rfl)

-- C1: rule cast-down accepts the type test instanceof MyFoo<X> from Foo<X>.
theorem c1 : Cast d2 [{ X := tn "X", T := obj }] (tFoo (.var (tn "X"))) (.cls (cn "MyFoo") [.var (tn "X")]) :=
  Cast.castDown (Xs := [tn "Y"]) (Ts' := [.var (tn "Y")])
    (Sub.subInheritLocal myFooDeclared rfl .subRefl)
    (Generic.loc myFooDeclared)
    (Sub.subInheritLocal myFooDeclared rfl .subRefl)
    (by intro X h; cases h with
      | head => exact .head _
      | tail _ h => cases h)

-- C2: rule cast-down rejects the type test instanceof MyFoo<X> from Object<>.
theorem c2 : Not (Cast d2 [{ X := tn "X", T := obj }] obj (.cls (cn "MyFoo") [.var (tn "X")])) := by
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
def stuckB : Expr := .superCall vA obj [] (mn "onlyB") []

-- W6: Example 1 in the core language is well formed.
theorem w6 : WFDecls d3 /\ WFExpr brokenMain := by decide

-- J2: Example 1 reduces to new A<>().onlyB(), then to new A<>().[Object<>]onlyB(), which is stuck.
theorem j2 : Steps d3 brokenMain stuckB /\ Stuck d3 stuckB := by
  sorry

-- N1: Example 1 is ill typed.
theorem n1 : Not (ProgOk d3 brokenMain) := by
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


-- L2: the class Leaker is not Ok.
theorem l2 : Not (ClassOk d4 decLeaker) := by
  sorry

def meth (Delta : Bounds) (T0 : Ty) (m : String) (ps : List VarDecl) (e : Expr) : Method := .mk Delta T0 (mn m) ps e
def par (T : Ty) (x : String) : VarDecl := { T := T, x := vn x }
def bnd (X : String) (T : Ty) : Bound := { X := tn X, T := T }
def ev (x : String) : Expr := .var (vn x)
def tv (X : String) : Ty := .var (tn X)
def call0 (e : Expr) (m : String) (es : List Expr) : Expr := .call e [] (mn m) es
def onlyBCall (e : Expr) : Expr := call0 e "onlyB" []

-- Example 1, funnelled as in Section 4.10.

def decFixed : Dec :=
  { C := cn "Fixed", bounds := [], C' := Object, Ts := [],
    Ms := [meth [bnd "X" obj] (tFoo (tv "X")) "mk" [par (tFoo (tv "X")) "other", par (tv "X") "x"]
      (.ifInst (ev "other") (.cls (cn "MyFoo") [tv "X"]) (vn "w") (ev "w")
        (.newLocal (cn "MyFoo") [.funnel (tn "X")] (cn "Foo") [tv "X"] [] [meth [] (tv "X") "x" [] (ev "x")]))],
    Ss := [] }

def d5 : Decls := [decObject, decA, decB, decFoo, decFixed]

def vMyFooA : Value := .newLocal (cn "MyFoo") [gA] (cn "Foo") [gA] [] [meth [] tA "x" [] vA]

def fixedCallA : Expr := .call (Value.new (cn "Fixed") [] []) [tA] (mn "mk") [Value.new (cn "Foo") [gA] [], vA]

-- W8: the funnelled Example 1 is well formed.
theorem w8 : WFDecls d5 := by decide

-- P1: the class Fixed is Ok.
theorem p1 : ClassOk d5 decFixed := by
  sorry

-- T3: new Fixed<>().<A<>>mk(new Foo<A<>>(), new A<>()) has type Foo<A<>>.
theorem t3 : Typing d5 [] [] fixedCallA (tFoo tA) := by
  sorry

-- R12: that call reduces to a MyFoo<A<>> whose method x returns new A<>().
theorem r12 : Steps d5 fixedCallA vMyFooA := by
  sorry

-- R13: given a MyFoo<A<>>, the type test succeeds and mk returns it.
theorem r13 : Steps d5 (.call (Value.new (cn "Fixed") [] []) [tA] (mn "mk") [vMyFooA, vA]) vMyFooA := by
  sorry

-- N2: the main expression of Example 1, with Fixed, is ill typed: a Foo<A<>> is passed where a Foo<B<>> is expected.
theorem n2 : Not (exists T, Typing d5 [] []
    (call0 (call0 (.call (Value.new (cn "Fixed") [] []) [tB] (mn "mk") [fixedCallA, vB]) "x" []) "onlyB" []) T) := by
  sorry

-- Examples 2 and 3: no generic supertype; the lambdas of the paper are subclasses of Fun.

def tFun (X Y : Ty) : Ty := .cls (cn "Fun") [X, Y]
def decFun : Dec :=
  { C := cn "Fun", bounds := [bnd "X" obj, bnd "Y" obj], C' := Object, Ts := [],
    Ms := [meth [] (tv "Y") "apply" [par (tv "X") "x"] (call0 thisE "apply" [ev "x"])], Ss := [] }
def decAToB : Dec :=
  { C := cn "AToB", bounds := [], C' := cn "Fun", Ts := [tA, tB],
    Ms := [meth [] tB "apply" [par tA "a"] vB], Ss := [] }
def decAsB : Dec :=
  { C := cn "AsB", bounds := [], C' := cn "Fun", Ts := [tB, tB],
    Ms := [meth [] tB "apply" [par tB "b"] (onlyBCall (ev "b"))], Ss := [] }
def vAToB : Value := .new (cn "AToB") [] []
def vAsB : Value := .new (cn "AsB") [] []

def decBroken2 : Dec :=
  { C := cn "Broken2", bounds := [], C' := Object, Ts := [],
    Ms := [meth [bnd "X" obj] obj "m" [par obj "other", par (tv "X") "x", par (tFun (tv "X") tB) "f"]
      (.ifInst (ev "other") (.cls (cn "MyFoo2") []) (vn "local") (call0 (ev "f") "apply" [call0 (ev "local") "x" []])
        (.newLocal (cn "MyFoo2") [] Object [] [] [meth [] (tv "X") "x" [] (ev "x")]))],
    Ss := [] }

def d6 : Decls := [decObject, decA, decB, decFun, decAToB, decAsB, decBroken2]

def main2 : Expr :=
  .call (Value.new (cn "Broken2") [] []) [tB] (mn "m")
    [.call (Value.new (cn "Broken2") [] []) [tA] (mn "m") [vA, vA, vAToB], vB, vAsB]

-- W9: Example 2 in the core language is well formed.
theorem w9 : WFDecls d6 /\ WFExpr main2 := by decide

-- N3: Example 2 is ill typed: the method x of MyFoo2 returns X, which MyFoo2 does not funnel.
theorem n3 : Not (ProgOk d6 main2) := by
  sorry

-- R14: Example 2 reduces to new A<>().[Object<>]onlyB(), which is stuck: AsB uses an A<> as a B<>.
theorem r14 : Steps d6 main2 stuckB /\ Stuck d6 stuckB := by
  sorry

def decHolder : Dec := { C := cn "Holder", bounds := [bnd "X" obj], C' := Object, Ts := [], Ms := [], Ss := [] }
def decFixed2 : Dec :=
  { C := cn "Fixed2", bounds := [], C' := Object, Ts := [],
    Ms := [meth [bnd "X" obj] obj "m" [par (.cls (cn "Holder") [tv "X"]) "other", par (tv "X") "x", par (tFun (tv "X") tB) "f"]
      (.ifInst (ev "other") (.cls (cn "MyFoo3") [tv "X"]) (vn "local") (call0 (ev "f") "apply" [call0 (ev "local") "x" []])
        (.newLocal (cn "MyFoo3") [.funnel (tn "X")] (cn "Holder") [tv "X"] [] [meth [] (tv "X") "x" [] (ev "x")]))],
    Ss := [] }
def decFixed2Obj : Dec :=
  { C := cn "Fixed2Obj", bounds := [], C' := Object, Ts := [],
    Ms := [meth [bnd "X" obj] obj "m" [par obj "other", par (tv "X") "x", par (tFun (tv "X") tB) "f"]
      (.ifInst (ev "other") (.cls (cn "MyFoo4") [tv "X"]) (vn "local") (call0 (ev "f") "apply" [call0 (ev "local") "x" []])
        (.newLocal (cn "MyFoo4") [.funnel (tn "X")] Object [] [] [meth [] (tv "X") "x" [] (ev "x")]))],
    Ss := [] }

def d6F : Decls := [decObject, decA, decB, decFun, decAToB, decAsB, decHolder, decFixed2, decFixed2Obj]

-- W10: the funnelled versions of Example 2 are well formed.
theorem w10 : WFDecls d6F := by decide

-- P2: funnelled, with other : Holder<X>, Example 2 is Ok: Holder<X> determines X.
theorem p2 : ClassOk d6F decFixed2 := by
  sorry

-- N4: funnelled, with other : Object<>, Example 2 is still ill typed: Object<> does not determine X.
theorem n4 : Not (ClassOk d6F decFixed2Obj) := by
  sorry

-- Example 6: X only in the methods of MyFoo6, and in the captured f.

def myFoo6 : Expr :=
  .newLocal (cn "MyFoo6") [] Object [] []
    [meth [] (tv "X") "v" [] (ev "x"),
     meth [] tB "show" [par (.cls (cn "MyFoo6") []) "o"] (call0 (ev "f") "apply" [call0 (ev "o") "v" []])]
def decBroken6 : Dec :=
  { C := cn "Broken6", bounds := [], C' := Object, Ts := [],
    Ms := [meth [bnd "X" obj] obj "m" [par obj "other", par (tv "X") "x", par (tFun (tv "X") tB) "f"]
        (call0 thisE "check" [myFoo6, ev "other"]),
      meth [] obj "check" [par (.cls (cn "MyFoo6") []) "mine", par obj "other"]
        (.ifInst (ev "other") (.cls (cn "MyFoo6") []) (vn "local") (call0 (ev "mine") "show" [ev "local"]) (ev "mine"))],
    Ss := [] }

def d7 : Decls := [decObject, decA, decB, decFun, decAToB, decAsB, decBroken6]

def main6 : Expr :=
  .call (Value.new (cn "Broken6") [] []) [tB] (mn "m")
    [.call (Value.new (cn "Broken6") [] []) [tA] (mn "m") [vA, vA, vAToB], vB, vAsB]

-- W11: Example 6 in the core language is well formed.
theorem w11 : WFDecls d7 /\ WFExpr main6 := by decide

-- N5: Example 6 is ill typed: MyFoo6 mentions X and captures f, but funnels nothing.
theorem n5 : Not (ProgOk d7 main6) := by
  sorry

-- R15: Example 6 reduces to new A<>().[Object<>]onlyB(), which is stuck.
theorem r15 : Steps d7 main6 stuckB /\ Stuck d7 stuckB := by
  sorry

-- Counterexample 7: class generics; javac rejects it, and so does funnelling.

def decBox7 : Dec :=
  { C := cn "Box7", bounds := [bnd "X" obj], C' := Object, Ts := [],
    Ms := [meth [] obj "m" [par obj "other", par (tv "X") "x", par (tFun (tv "X") tB) "f"]
      (.ifInst (ev "other") (.cls (cn "MyFoo7") []) (vn "local") (call0 (ev "f") "apply" [call0 (ev "local") "x" []])
        (.newLocal (cn "MyFoo7") [] Object [] [] [meth [] (tv "X") "x" [] (ev "x")]))],
    Ss := [] }
def decBox7F : Dec :=
  { C := cn "Box7F", bounds := [bnd "X" obj], C' := Object, Ts := [],
    Ms := [meth [] obj "m" [par obj "other", par (tv "X") "x", par (tFun (tv "X") tB) "f"]
      (.ifInst (ev "other") (.cls (cn "MyFoo7F") [tv "X"]) (vn "local") (call0 (ev "f") "apply" [call0 (ev "local") "x" []])
        (.newLocal (cn "MyFoo7F") [.funnel (tn "X")] Object [] [] [meth [] (tv "X") "x" [] (ev "x")]))],
    Ss := [] }

def d8 : Decls := [decObject, decA, decB, decFun, decAToB, decAsB, decBox7, decBox7F]

def main7 : Expr :=
  .call (Value.new (cn "Box7") [gB] []) [] (mn "m")
    [.call (Value.new (cn "Box7") [gA] []) [] (mn "m") [vA, vA, vAToB], vB, vAsB]

-- W12: Counterexample 7 is well formed.
theorem w12 : WFDecls d8 /\ WFExpr main7 := by decide

-- N6: Counterexample 7 is ill typed: MyFoo7 does not funnel the class type variable X.
theorem n6 : Not (ClassOk d8 decBox7) := by
  sorry

-- N7: funnelled, Counterexample 7 is still ill typed: Object<> does not determine X; javac reports this error too.
theorem n7 : Not (ClassOk d8 decBox7F) := by
  sorry

-- R16: Counterexample 7 reduces as Example 2: to new A<>().[Object<>]onlyB(), which is stuck.
theorem r16 : Steps d8 main7 stuckB /\ Stuck d8 stuckB := by
  sorry

-- The method leak of Section 4.10.

def leakMain : Expr :=
  onlyBCall (call0 (.call (Value.new (cn "Leaker") [] []) [tB] (mn "leak")
    [.call (Value.new (cn "Leaker") [] []) [tA] (mn "mk2") [vA]]) "x" [])

-- R17: leak returns a MyFoo2 built with A<> as a Foo<B<>>; the program reduces to new A<>().[Object<>]onlyB(), which is stuck.
theorem r17 : Steps d4 leakMain stuckB /\ Stuck d4 stuckB := by
  sorry

def decLeakerF : Dec :=
  { C := cn "LeakerF", bounds := [], C' := Object, Ts := [],
    Ms := [
      meth [bnd "Y" obj] (.cls (cn "MyFoo2F") [tv "Y"]) "mk2" [par (tv "Y") "y"]
        (.newLocal (cn "MyFoo2F") [.funnel (tn "Y")] (cn "Foo") [tv "Y"] [] [meth [] (tv "Y") "x" [] (ev "y")]),
      meth [bnd "Y" obj] (tFoo (tv "Y")) "leak" [par (.cls (cn "MyFoo2F") [tv "Y"]) "z"] (ev "z")],
    Ss := [] }

def d4F : Decls := [decObject, decA, decB, decFoo, decLeakerF]

def leakMainF : Expr :=
  onlyBCall (call0 (.call (Value.new (cn "LeakerF") [] []) [tB] (mn "leak")
    [.call (Value.new (cn "LeakerF") [] []) [tA] (mn "mk2") [vA]]) "x" [])

-- W13: the funnelled leak is well formed.
theorem w13 : WFDecls d4F := by decide

-- P3: funnelled, the class LeakerF is Ok: leak takes a MyFoo2F<Y> and returns a Foo<Y>.
theorem p3 : ClassOk d4F decLeakerF := by
  sorry

-- N8: funnelled, the main expression of the leak is ill typed: a MyFoo2F<A<>> is passed where a MyFoo2F<B<>> is expected.
theorem n8 : Not (exists T, Typing d4F [] [] leakMainF T) := by
  sorry

-- Nested local classes: Inner is written in a method of Outer.

def innerExpr : Expr :=
  .newLocal (cn "Inner") [.funnel (tn "X")] (cn "Foo") [tv "X"] [] [meth [] (tv "X") "x" [] (ev "x")]
def outerMethod : Method := meth [] (tv "X") "x" [] (call0 innerExpr "x" [])
def outerExpr : Expr := .newLocal (cn "Outer") [.funnel (tn "X")] (cn "Foo") [tv "X"] [] [outerMethod]
def nestMk : Method := meth [bnd "X" obj] (tFoo (tv "X")) "mk" [par (tv "X") "x"] outerExpr
def decNest : Dec := { C := cn "Nest", bounds := [], C' := Object, Ts := [], Ms := [nestMk], Ss := [] }

def d9 : Decls := [decObject, decA, decB, decFoo, decNest]

def outerK : K := .loc (cn "Outer") [.funnel (tn "X")] (cn "Foo") [tv "X"] [] [outerMethod]
def innerK : K := .loc (cn "Inner") [.funnel (tn "X")] (cn "Foo") [tv "X"] [] [meth [] (tv "X") "x" [] (ev "x")]

-- W14: nested local classes are well formed.
theorem w14 : WFDecls d9 := by decide

theorem nestDeclared : Declared d9 (.dec decNest) := .dec (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

theorem outerDeclared : Declared d9 outerK :=
  Declared.loc (k := .dec decNest) nestDeclared (.head _) (Exists.intro .hole rfl)

-- D1: Inner is declared: it occurs in the method x of Outer, which occurs in the method mk of Nest.
theorem d1Inner : Declared d9 innerK :=
  Declared.loc (k := outerK) outerDeclared (.head _) (Exists.intro (.callRecv .hole [] (mn "x") []) rfl)

theorem scopeOuter : Scope d9 (.cls (cn "Outer") [tv "X"]) [bnd "X" obj] [tv "X"] :=
  Scope.loc (C := cn "Nest") (T := .cls (cn "Nest") []) (Delta := []) (Ts'' := [])
    (Exists.intro (.dec decNest) (And.intro nestDeclared (And.intro rfl (.head _))))
    (Exists.intro .hole rfl) (Generic.dec nestDeclared) (Scope.dec nestDeclared) (Pairing.funnel (.head _) .nil)

theorem kindA9 : Kind d9 [] tA :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decA) (.dec (.tail _ (.head _))))
    (by intro T h; cases h) rfl .nil

theorem subAObj9 : Sub d9 [] tA obj := Sub.subInherit (D := decA) (.dec (.tail _ (.head _))) rfl .subRefl

-- K1: Inner<A<>> is well kinded: its scope goes through the scope of Outer<X>.
theorem k1 : Kind d9 [] (.cls (cn "Inner") [tA]) :=
  Kind.wfClass (Delta0 := [bnd "X" obj]) (Ts0 := [tA])
    (Scope.loc (C := cn "Outer") (T := .cls (cn "Outer") [tv "X"]) (Delta := [bnd "X" obj]) (Ts'' := [tv "X"])
      (Exists.intro outerK (And.intro outerDeclared (And.intro rfl (.head _))))
      (Exists.intro (.callRecv .hole [] (mn "x") []) rfl)
      (Generic.loc outerDeclared) scopeOuter (Pairing.funnel (.head _) .nil))
    (by intro T h; cases h with
      | head => exact kindA9
      | tail _ h => cases h)
    rfl (.cons subAObj9 .nil)

-- R18: new Nest<>().<A<>>mk(new A<>()).x() reduces to new A<>().
theorem r18 : Steps d9 (call0 (.call (Value.new (cn "Nest") [] []) [tA] (mn "mk") [vA]) "x" []) vA := by
  sorry

-- Funnels of both forms: after mk<A<>>, the value of Outer2 holds Inner2<Y funnel>, with Y a type variable of g.

def inner2Expr : Expr :=
  .newLocal (cn "Inner2") [.funnel (tn "Y")] (cn "Foo") [tv "Y"] [] [meth [] (tv "Y") "x" [] (ev "y")]
def decMix : Dec :=
  { C := cn "Mix", bounds := [], C' := Object, Ts := [],
    Ms := [meth [bnd "X" obj] (tFoo (tv "X")) "mk" [par (tv "X") "x"]
      (.newLocal (cn "Outer2") [.funnel (tn "X")] (cn "Foo") [tv "X"] []
        [meth [] (tv "X") "x" [] (ev "x"),
         meth [bnd "Y" obj] (tFoo (tv "Y")) "g" [par (tv "Y") "y"] inner2Expr])],
    Ss := [] }

def d10 : Decls := [decObject, decA, decB, decFoo, decMix]

def vOuter2A : Value :=
  .newLocal (cn "Outer2") [gA] (cn "Foo") [gA] []
    [meth [] tA "x" [] vA, meth [bnd "Y" obj] (tFoo (tv "Y")) "g" [par (tv "Y") "y"] inner2Expr]

-- W15: the class table with Outer2 and Inner2 is well formed.
theorem w15 : WFDecls d10 := by decide

-- W16: the value of Outer2<A<>> is well formed; it holds the ground funnel A<> and the funnel Y funnel.
theorem w16 : WFExpr vOuter2A := by decide

-- R19: calling g<B<>> on the value of Outer2<A<>> gives an Inner2<B<>> whose method x returns new B<>().
theorem r19 : Steps d10 (.call vOuter2A [tB] (mn "g") [vB])
    (Value.newLocal (cn "Inner2") [gB] (cn "Foo") [gB] [] [meth [] tB "x" [] vB]) := by
  sorry

-- Overriding.

def p1Id : Method := meth [bnd "X" obj] (tv "X") "id" [par (tv "X") "x"] (ev "x")
def p2Id : Method := meth [bnd "Z" obj] (tv "Z") "id" [par (tv "Z") "z"] (ev "z")
def p3Id : Method := meth [bnd "Z" obj] obj "id" [par (tv "Z") "z"] (ev "z")
def p4Id : Method := meth [bnd "Z" tA] (tv "Z") "id" [par (tv "Z") "z"] (ev "z")
def decP1 : Dec := { C := cn "P1", bounds := [], C' := Object, Ts := [], Ms := [p1Id], Ss := [] }
def decP2 : Dec := { C := cn "P2", bounds := [], C' := cn "P1", Ts := [], Ms := [p2Id], Ss := [] }
def decP3 : Dec := { C := cn "P3", bounds := [], C' := cn "P1", Ts := [], Ms := [p3Id], Ss := [] }
def decP4 : Dec := { C := cn "P4", bounds := [], C' := cn "P1", Ts := [], Ms := [p4Id], Ss := [] }

def d11 : Decls := [decObject, decA, decP1, decP2, decP3, decP4]

-- W17: the overriding examples are well formed.
theorem w17 : WFDecls d11 := by decide

-- O1: P2 overrides id with its type variable renamed: Z for X.
theorem o1 : OverrideOkM d11 (.cls (cn "P1") []) p2Id :=
  OverrideOkM.dec (D := decP1) (Delta'' := [bnd "X" obj]) (T0 := tv "X") (ps := [par (tv "X") "x"]) (e := ev "x")
    (.dec (.tail _ (.tail _ (.head _)))) (.head _) rfl rfl rfl rfl

-- O2: P3 changes the return type of id.
theorem o2 : Not (OverrideOkM d11 (.cls (cn "P1") []) p3Id) := by
  sorry

-- O3: P2 is Ok.
theorem o3 : ClassOk d11 decP2 := by
  sorry

-- O4: P3 and P4 are not Ok: P3 changes the return type, P4 changes the bound of the type variable.
theorem o4 : Not (ClassOk d11 decP3) /\ Not (ClassOk d11 decP4) := by
  sorry

-- Checked casts.

-- C3: rule cast-var, then rule cast-down: from X extends Foo<A<>> to MyFoo<A<>>.
theorem c3 : Cast d2 [bnd "X" (tFoo tA)] (tv "X") (.cls (cn "MyFoo") [tA]) :=
  Cast.castVar (.head _)
    (Cast.castDown (Xs := [tn "Y"]) (Ts' := [tv "Y"])
      (Sub.subInheritLocal myFooDeclared rfl .subRefl)
      (Generic.loc myFooDeclared)
      (Sub.subInheritLocal myFooDeclared rfl .subRefl)
      (by intro X h; cases h with
        | head => exact .head _
        | tail _ h => cases h))

-- C4: rule cast-up: from B<> to Object<>.
theorem c4 : Cast d1 [] tB obj := Cast.castUp (Sub.subInherit (D := decB) (.dec (.tail _ (.tail _ (.head _)))) rfl .subRefl)

-- C5: no checked cast between unrelated classes: from A<> to B<>.
theorem c5 : Not (Cast d1 [] tA tB) := by
  sorry

-- Fields of a superclass.

def decBase : Dec :=
  { C := cn "Base", bounds := [bnd "X" obj], C' := Object, Ts := [], Ms := [], Ss := [{ T := tv "X", f := fn "f" }] }
def decDerived : Dec :=
  { C := cn "Derived", bounds := [], C' := cn "Base", Ts := [tA], Ms := [], Ss := [{ T := tB, f := fn "g" }] }

def d12 : Decls := [decObject, decA, decB, decBase, decDerived]

def derivedF : Expr := .field (Value.new (cn "Derived") [] [vB, vA]) (fn "f")

theorem declBase : Declared d12 (.dec decBase) := .dec (.tail _ (.tail _ (.tail _ (.head _))))
theorem declDerived : Declared d12 (.dec decDerived) := .dec (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

-- R20: the field f of a Derived<> is the field of its superclass Base<A<>>: two steps.
theorem r20 : Steps d12 derivedF vA :=
  Steps.step
    (And.intro
      (Step.simpleFieldSuper (D := decDerived) (Gs := []) (vs1 := [vB]) (vs := [vA]) declDerived rfl
        (by decide) (by decide) rfl)
      (by decide))
    (Steps.step
      (And.intro
        (Step.simpleFieldFound (D := decBase) (Gs := [gA]) (vs1 := [vA]) (vs := []) declBase rfl (.head _))
        (by decide))
      Steps.refl)

theorem kindA12 : Kind d12 [] tA :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decA) (.dec (.tail _ (.head _))))
    (by intro T h; cases h) rfl .nil

theorem kindB12 : Kind d12 [] tB :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decB) (.dec (.tail _ (.tail _ (.head _)))))
    (by intro T h; cases h) rfl .nil

theorem kindBaseA : Kind d12 [] (.cls (cn "Base") [tA]) :=
  Kind.wfClass (Delta0 := decBase.bounds) (Ts0 := [tA]) (Scope.dec declBase)
    (by intro T h; cases h with
      | head => exact kindA12
      | tail _ h => cases h)
    rfl (.cons (Sub.subInherit (D := decA) (.dec (.tail _ (.head _))) rfl .subRefl) .nil)

theorem kindDerived : Kind d12 [] (.cls (cn "Derived") []) :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec declDerived) (by intro T h; cases h) rfl .nil

theorem typA12 : Typing d12 [] [] vA tA :=
  Typing.newTop (D := decA) (es1 := []) (es2 := []) (.dec (.tail _ (.head _))) kindA12 rfl .nil Typing.newObject

theorem typB12 : Typing d12 [] [] vB tB :=
  Typing.newTop (D := decB) (es1 := []) (es2 := []) (.dec (.tail _ (.tail _ (.head _)))) kindB12 rfl .nil
    Typing.newObject

theorem typDerived : Typing d12 [] [] (Value.new (cn "Derived") [] [vB, vA]) (.cls (cn "Derived") []) :=
  Typing.newTop (D := decDerived) (es1 := [vB]) (es2 := [vA]) declDerived kindDerived rfl (.cons typB12 .nil)
    (Typing.newTop (D := decBase) (es1 := [vA]) (es2 := []) declBase kindBaseA rfl (.cons typA12 .nil)
      Typing.newObject)

-- T4: the field f of a Derived<> has type A<>: rule subs to Base<A<>>, then rule declField.
theorem t4 : Typing d12 [] [] derivedF tA :=
  Typing.declField (D := decBase) (Ts' := [tA]) (T := tv "X")
    (Typing.subs typDerived kindBaseA (Sub.subInherit (D := decDerived) declDerived rfl .subRefl))
    declBase (.head _) rfl

-- Well-formedness requirements one by one.

-- W18: A2: a field f in both Derived2 and its superclass Base.
theorem w18 : Not (WFDecls [decObject, decA, decBase,
    { C := cn "Derived2", bounds := [], C' := cn "Base", Ts := [tA], Ms := [], Ss := [{ T := tB, f := fn "f" }] }]) := by
  decide

-- W19: A1: a local class named A, as the top-level class A.
theorem w19 : Not (WFDecls [decObject, decA,
    { C := cn "Clash", bounds := [], C' := Object, Ts := [],
      Ms := [meth [] obj "m" [] (.newLocal (cn "A") [] Object [] [] [])], Ss := [] }]) := by
  decide

-- W20: A11: a ground funnel in Decls.
theorem w20 : Not (WFDecls [decObject, decA,
    { C := cn "Ground", bounds := [], C' := Object, Ts := [],
      Ms := [meth [] obj "m" [] (.newLocal (cn "L") [.ground gA] Object [] [] [])], Ss := [] }]) := by
  decide

-- W21: A6: the same type variable funnelled twice.
theorem w21 : Not (WFDecls [decObject,
    { C := cn "Twice", bounds := [], C' := Object, Ts := [],
      Ms := [meth [bnd "X" obj] obj "m" [] (.newLocal (cn "L") [.funnel (tn "X"), .funnel (tn "X")] Object [] [] [])],
      Ss := [] }]) := by
  decide

-- W22: A8: a parameter named this.
theorem w22 : Not (WFDecls [decObject,
    { C := cn "Self", bounds := [], C' := Object, Ts := [], Ms := [meth [] obj "m" [par obj "this"] thisE], Ss := [] }]) := by
  decide

-- W23: A9: a cycle of superclasses.
theorem w23 : Not (WFDecls [decObject,
    { C := cn "C3", bounds := [], C' := cn "C4", Ts := [], Ms := [], Ss := [] },
    { C := cn "C4", bounds := [], C' := cn "C3", Ts := [], Ms := [], Ss := [] }]) := by
  decide

-- Renaming by fresh.

def nestedIf : Expr := .ifInst (ev "x") tA (vn "y") (ev "y") (ev "x")
def nestedIf' : Expr := .ifInst (ev "x") tA (vn "y1") (ev "y1") (ev "x")

-- R21: rule ifThen renames the variable y of the inner if into y1, then replaces x.
theorem r21 : Reduces d1 (.ifInst vA tA (vn "x") nestedIf vB) (.ifInst vA tA (vn "y1") (ev "y1") vA) :=
  And.intro
    (Step.ifThen (v := vA) (C' := cn "A") (Ts := []) (Ts' := []) (x := vn "x") (e1 := nestedIf) (e1' := nestedIf')
      (e2 := vB) .subRefl (And.intro (RenE.ifInst .var .var .var) (RenE.ifInst .var .var .var)) (by decide))
    (by decide)

-- The example of Section 4.4: a local class L whose method m calls m on a captured value y of class L.

def lMethod : Method := meth [] obj "m" [par obj "x"] (call0 (ev "y") "m" [ev "x"])
def decK : Dec :=
  { C := cn "K", bounds := [], C' := Object, Ts := [],
    Ms := [meth [] obj "k" [par (.cls (cn "L") []) "y"] (.newLocal (cn "L") [] Object [] [] [lMethod])], Ss := [] }

def d13 : Decls := [decObject, decK]

def vL : Value := .newLocal (cn "L") [] Object [] [] [meth [] obj "m" [par obj "x"] (ev "x")]

def kResult : Value := .newLocal (cn "L") [] Object [] [] [meth [] obj "m" [par obj "x1"] (call0 vL "m" [ev "x1"])]

-- W24: without renaming, the body of k with vL for y would bind x inside a method binding x, against A7.
theorem w24 : Not (WFExpr (Value.newLocal (cn "L") [] Object [] [] [meth [] obj "m" [par obj "x"] (call0 vL "m" [ev "x"])])) := by
  decide

-- R22: rule simpleFound renames y into y1 and x into x1, so the copy of m binds x1 and the result is well formed.
theorem r22 : Steps d13 (call0 (Value.new (cn "K") [] []) "k" [vL]) kResult :=
  Steps.step (And.intro (Step.simpleAddSuper (Gs' := []) (vs := [vL]) rfl) (by decide))
    (Steps.step
      (And.intro
        (Step.simpleFound (D := decK) (M := meth [] obj "k" [par (.cls (cn "L") []) "y"]
            (.newLocal (cn "L") [] Object [] [] [lMethod]))
          (Gs := []) (Gs' := []) (vs := [vL]) (Delta' := []) (T0 := obj) (ps := [par (.cls (cn "L") []) "y1"])
          (e0 := .newLocal (cn "L") [] Object [] [] [meth [] obj "m" [par obj "x1"] (call0 (ev "y1") "m" [ev "x1"])])
          (.dec (.tail _ (.head _))) (.head _)
          (And.intro
            (.mk (Xs' := []) (xs' := [vn "y1"]) rfl rfl
              (.newLocal .nil (.cons (.mk (Xs' := []) (xs' := [vn "x1"]) rfl rfl (.call .var (.cons .var .nil))) .nil)))
            (.mk (Xs' := []) (xs' := [vn "y"]) rfl rfl
              (.newLocal .nil (.cons (.mk (Xs' := []) (xs' := [vn "x"]) rfl rfl (.call .var (.cons .var .nil))) .nil))))
          rfl rfl (by decide) (by decide) rfl (by decide) (by decide) rfl)
        (by decide))
      Steps.refl)

-- S1: field access on new Object<>() is stuck.
theorem s1 : Stuck d1 (.field (Value.new Object [] []) (fn "f")) := by
  sorry

-- The bug of plain alpha-renaming with a substitution that enters a binder of x.

def innerIf (y : String) : Expr := .ifInst vB tB (vn y) (call0 (ev y) "onlyB" []) vB
def outerIf : Expr := .ifInst vA tA (vn "x") (innerIf "y") vB

-- W25: renaming y into x makes the substitution [x = new A<>()] undefined, so rule ifThen has no such instance.
theorem w25 : Not (VSubstDefined [vn "x"] (innerIf "x")) := by decide

-- R23: renaming y into y1, the program reduces to new B<>() in four steps.
theorem r23 : Steps d1 outerIf vB :=
  Steps.step
    (And.intro
      (Step.ifThen (v := vA) (C' := cn "A") (Ts := []) (Ts' := []) (x := vn "x") (e1 := innerIf "y")
        (e1' := innerIf "y1") (e2 := vB) .subRefl
        (And.intro (RenE.ifInst (.new .nil) (.call .var .nil) (.new .nil)) (RenE.ifInst (.new .nil) (.call .var .nil) (.new .nil)))
        (by decide))
      (by decide))
    (Steps.step
      (And.intro
        (Step.ifThen (v := vB) (C' := cn "B") (Ts := []) (Ts' := []) (x := vn "y1")
          (e1 := call0 (ev "y1") "onlyB" []) (e1' := call0 (ev "y1") "onlyB" []) (e2 := vB) .subRefl
          (And.intro (.call .var .nil) (.call .var .nil)) (by decide))
        (by decide))
      (Steps.step
        (And.intro (Step.simpleAddSuper (Gs' := []) (vs := []) rfl) (by decide))
        (Steps.step
          (And.intro
            (Step.simpleFound (D := decB) (M := meth [] tB "onlyB" [] vB) (Gs := []) (Gs' := []) (vs := [])
              (Delta' := []) (T0 := tB) (ps := []) (e0 := vB)
              (.dec (.tail _ (.tail _ (.head _)))) (.head _)
              (And.intro (.mk (Xs' := []) (xs' := []) rfl rfl (.new .nil)) (.mk (Xs' := []) (xs' := []) rfl rfl (.new .nil)))
              rfl rfl (by decide) (by decide) rfl (by decide) (by decide) rfl)
            (by decide))
          Steps.refl)))

-- The hypotheses of typeSoundness hold together: DeclsOk for d1 and for d2.

theorem localsList_append (a b : List Expr) :
    Expr.localsList (a ++ b) = Expr.localsList a ++ Expr.localsList b := by
  induction a with
  | nil => simp [Expr.localsList]
  | cons x xs ih => simp [Expr.localsList, ih]

theorem one {A : Type} {a b : A} (h : List.Mem a [b]) : a = b := by
  cases h with
  | head => rfl
  | tail _ h => cases h

theorem noMem {A : Type} {a : A} (h : List.Mem a []) : False := by cases h

theorem occurs_mem (ctx : ExprCtx) (C0 Fs C' Ts es Ms) :
    List.Mem (K.loc C0 Fs C' Ts es Ms) (ctx.plug (.newLocal C0 Fs C' Ts es Ms)).locals := by
  have key : forall l : List K, Membership.mem l (K.loc C0 Fs C' Ts es Ms) -> List.Mem (K.loc C0 Fs C' Ts es Ms) l :=
    fun _ h => h
  apply key
  induction ctx with
  | hole => simp [ExprCtx.plug, Expr.locals]
  | callRecv ctx _ _ _ ih => simp [ExprCtx.plug, Expr.locals, ih]
  | callArg _ _ _ _ ctx _ ih => simp [ExprCtx.plug, Expr.locals, localsList_append, Expr.localsList, ih]
  | superRecv ctx _ _ _ _ ih => simp [ExprCtx.plug, Expr.locals, ih]
  | superArg _ _ _ _ _ ctx _ ih => simp [ExprCtx.plug, Expr.locals, localsList_append, Expr.localsList, ih]
  | field ctx _ ih => simp [ExprCtx.plug, Expr.locals, ih]
  | newArg _ _ _ ctx _ ih => simp [ExprCtx.plug, Expr.locals, localsList_append, Expr.localsList, ih]
  | localArg _ _ _ _ _ ctx _ _ ih => simp [ExprCtx.plug, Expr.locals, localsList_append, Expr.localsList, ih]
  | ifCond ctx _ _ _ _ ih => simp [ExprCtx.plug, Expr.locals, ih]
  | ifThen _ _ _ ctx _ ih => simp [ExprCtx.plug, Expr.locals, ih]
  | ifElse _ _ _ _ ctx ih => simp [ExprCtx.plug, Expr.locals, ih]

namespace OkD1

theorem bodies : forall D, List.Mem D d1 -> forall M, List.Mem M D.Ms -> M.body.locals.isEmpty = true := by
  decide

theorem declared {k} (h : Declared d1 k) : exists D, k = .dec D /\ List.Mem D d1 := by
  induction h with
  | dec hD => exact Exists.intro _ (And.intro rfl hD)
  | @loc k Delta T0 m ps e C0 Fs C' Ts es Ms _ hM hOcc ih =>
    cases ih with
    | intro D hk =>
    cases hk with
    | intro hk hD =>
    subst hk
    cases hOcc with
    | intro ctx hctx =>
    have hmem := occurs_mem ctx C0 Fs C' Ts es Ms
    rw [<- hctx] at hmem
    have h1 := bodies D hD _ hM
    simp [Method.body] at h1
    rw [h1] at hmem
    exact absurd hmem (fun h => noMem h)

theorem objDec {D} (h : Declared d1 (.dec D)) (hC : D.C = Object) : D = decObject := by
  cases h with
  | dec hmem =>
    have hm : Membership.mem d1 D := hmem
    simp [d1] at hm
    rcases hm with h | h | h | h | h | h <;> subst h <;>
      first | rfl | (simp [decA, decB, decBox, decC1, decC2, cn, Object] at hC)

theorem subObject {Delta S T} (h : Sub d1 Delta S T) : S = .cls Object [] -> T = .cls Object [] := by
  induction h with
  | subRefl => exact id
  | @subInherit D Ts0 T' hD _ _ ih =>
    intro hS
    injection hS with hC hTs
    have := objDec hD hC
    subst this
    subst hTs
    exact ih rfl
  | subInheritLocal hD _ _ _ =>
    intro _
    cases declared hD with
    | intro D h2 => exact absurd h2.1 (fun e => by cases e)
  | subVar _ _ _ => intro hS; cases hS

theorem kObj (Delta : Bounds) : Kind d1 Delta obj :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decObject) (.dec (.head _)))
    (by intro T h; cases h) rfl .nil

theorem overrideObj (Delta : Bounds) (Ms : List Method) : OverrideOk d1 Delta obj Ms := by
  intro M C Ts _ hs
  have := subObject hs rfl
  cases this
  cases M with
  | mk _ _ m _ _ => exact OverrideOkM.absent (D := decObject) (.dec (.head _)) (by intro h; cases h)

theorem kB : Kind d1 [] tB :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decB) (.dec (.tail _ (.tail _ (.head _)))))
    (by intro T h; cases h) rfl .nil

theorem kC1 : Kind d1 [] (.cls (cn "C1") []) :=
  Kind.wfClass (Delta0 := []) (Ts0 := [])
    (Scope.dec (D := decC1) (.dec (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    (by intro T h; cases h) rfl .nil

theorem kX : Kind d1 [bnd "X" obj] (tv "X") := Kind.wfVar (T := obj) (.head _)

theorem okObject : ClassOk d1 decObject :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kObj _) (And.intro (by intro M h; cases h) (overrideObj _ _)))

theorem okA : ClassOk d1 decA :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kObj _) (And.intro (by intro M h; cases h) (overrideObj _ _)))

theorem okB : ClassOk d1 decB :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kObj _)
      (And.intro
        (by
          intro M h
          rw [one h]
          exact MethodOk.methodOk (by intro T h; cases h) (by intro T h; rw [one h]; exact kB)
            (Typing.newTop (D := decB) (es1 := []) (es2 := []) (.dec (.tail _ (.tail _ (.head _)))) kB rfl .nil
              Typing.newObject))
        (overrideObj _ _)))

theorem okC1 : ClassOk d1 decC1 :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kObj _)
      (And.intro
        (by
          intro M h
          rw [one h]
          exact MethodOk.methodOk (by intro T h; cases h) (by intro T h; rw [one h]; exact kindA)
            (Typing.newTop (D := decA) (es1 := []) (es2 := []) (.dec (.tail _ (.head _))) kindA rfl .nil Typing.newObject))
        (overrideObj _ _)))

theorem okC2 : ClassOk d1 decC2 :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kC1) (And.intro (by intro M h; cases h) (by intro M C Ts h; cases h)))

theorem okBox : ClassOk d1 decBox :=
  And.intro (by intro T h; rw [one h]; exact kObj _)
    (And.intro
      (by
        intro T h
        cases h with
        | head => exact kObj _
        | tail _ h => rw [one h]; exact kX)
      (And.intro
        (by
          intro M h
          rw [one h]
          exact MethodOk.methodOk (by intro T h; cases h) (by intro T h; rw [one h]; exact kX)
            (Typing.declField (D := decBox) (Ts' := [tv "X"]) (T := tv "X")
              (Typing.var rfl) (.dec (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) rfl))
        (overrideObj _ _)))

theorem declsOk : DeclsOk d1 := by
  intro D h
  have hm : Membership.mem d1 D := h
  simp [d1] at hm
  rcases hm with h | h | h | h | h | h <;> subst h <;>
    first | exact okObject | exact okA | exact okB | exact okBox | exact okC1 | exact okC2

end OkD1

namespace OkD2

theorem bodies : forall D, List.Mem D d2 -> Not (D.C = cn "Maker") -> forall M, List.Mem M D.Ms ->
    M.body.locals.isEmpty = true := by
  decide

theorem declared {k} (h : Declared d2 k) : (exists D, k = .dec D /\ List.Mem D d2) \/ k = myFooK := by
  induction h with
  | dec hD => exact Or.inl (Exists.intro _ (And.intro rfl hD))
  | @loc k Delta T0 m ps e C0 Fs C' Ts es Ms _ hM hOcc ih =>
    cases hOcc with
    | intro ctx hctx =>
    have hmem := occurs_mem ctx C0 Fs C' Ts es Ms
    rw [<- hctx] at hmem
    cases ih with
    | inl h =>
      cases h with
      | intro D hk =>
      cases hk with
      | intro hk hD =>
      subst hk
      by_cases hC : D.C = cn "Maker"
      case pos =>
        have hDm : Membership.mem d2 D := hD
        simp [d2] at hDm
        rcases hDm with h | h | h | h | h <;> subst h <;> simp [decObject, decA, decB, decFoo, cn, Object] at hC
        have hm := one hM
        simp only [mkMethod] at hm
        cases hm
        have h2 : List.Mem (K.loc C0 Fs C' Ts es Ms) [myFooK] := by
          simpa [myFooK, myFooBody, Expr.locals, Expr.localsList, Method.localsList, myFooMethod, Method.locals]
            using hmem
        exact Or.inr (one h2)
      case neg =>
        have h1 := bodies D hD hC _ hM
        simp [Method.body] at h1
        rw [h1] at hmem
        exact absurd hmem (fun h => noMem h)
    | inr hk =>
      subst hk
      have hm := one hM
      simp only [myFooMethod] at hm
      cases hm
      exact absurd hmem (fun h => noMem (by simpa [Expr.locals] using h))

theorem decName {D C} (h : Declared d2 (.dec D)) (hC : D.C = C) :
    (C = Object -> D = decObject) /\ (C = cn "Foo" -> D = decFoo) := by
  cases h with
  | dec hmem =>
    have hm : Membership.mem d2 D := hmem
    simp [d2] at hm
    subst hC
    rcases hm with h | h | h | h | h <;> subst h <;> simp [decObject, decA, decB, decFoo, decMaker, cn, Object]

theorem locName {C Fs C' Ts es Ms} (h : Declared d2 (.loc C Fs C' Ts es Ms)) : C = cn "MyFoo" := by
  cases declared h with
  | inl h1 =>
    cases h1 with
    | intro D h2 => exact absurd h2.1 (fun e => by cases e)
  | inr hk => simp [myFooK] at hk; exact hk.1

theorem subObject {Delta S T} (h : Sub d2 Delta S T) : S = .cls Object [] -> T = .cls Object [] := by
  induction h with
  | subRefl => exact id
  | @subInherit D Ts0 T' hD _ _ ih =>
    intro hS
    injection hS with hC hTs
    have := (decName hD hC).1 rfl
    subst this
    subst hTs
    exact ih rfl
  | subInheritLocal hD _ _ _ =>
    intro hS
    injection hS with hC
    have := locName hD
    rw [this] at hC
    simp [cn, Object] at hC
  | subVar _ _ _ => intro hS; cases hS

theorem subFoo {Delta S T T0} (h : Sub d2 Delta S T) :
    S = .cls (cn "Foo") [T0] -> T = .cls (cn "Foo") [T0] \/ T = .cls Object [] := by
  induction h with
  | subRefl => intro h; exact Or.inl h
  | @subInherit D Ts0 T' hD _ hs _ =>
    intro hS
    injection hS with hC hTs
    have := (decName hD hC).2 rfl
    subst this
    exact Or.inr (subObject hs rfl)
  | subInheritLocal hD _ _ _ =>
    intro hS
    injection hS with hC
    have := locName hD
    rw [this] at hC
    simp [cn] at hC
  | subVar _ _ _ => intro hS; cases hS

theorem declObj : Declared d2 (.dec decObject) := .dec (.head _)
theorem declA : Declared d2 (.dec decA) := .dec (.tail _ (.head _))
theorem declB : Declared d2 (.dec decB) := .dec (.tail _ (.tail _ (.head _)))
theorem declFoo : Declared d2 (.dec decFoo) := .dec (.tail _ (.tail _ (.tail _ (.head _))))
theorem declMaker : Declared d2 (.dec decMaker) := .dec (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

theorem kObj (Delta : Bounds) : Kind d2 Delta obj :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decObject) declObj) (by intro T h; cases h) rfl .nil
theorem kA (Delta : Bounds) : Kind d2 Delta tA :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decA) declA) (by intro T h; cases h) rfl .nil
theorem kB (Delta : Bounds) : Kind d2 Delta tB :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decB) declB) (by intro T h; cases h) rfl .nil
theorem kMaker (Delta : Bounds) : Kind d2 Delta (.cls (cn "Maker") []) :=
  Kind.wfClass (Delta0 := []) (Ts0 := []) (Scope.dec (D := decMaker) declMaker) (by intro T h; cases h) rfl .nil

theorem overrideObj (Delta : Bounds) (Ms : List Method) : OverrideOk d2 Delta obj Ms := by
  intro M C Ts _ hs
  have := subObject hs rfl
  cases this
  cases M with
  | mk _ _ m _ _ => exact OverrideOkM.absent (D := decObject) declObj (by intro h; cases h)

def dY : Bounds := [bnd "Y" obj]
def dX : Bounds := [bnd "X" obj]

theorem kFoo (Delta : Bounds) (T : Ty) (hk : Kind d2 Delta T) (hs : Sub d2 Delta T obj) :
    Kind d2 Delta (tFoo T) :=
  Kind.wfClass (Delta0 := decFoo.bounds) (Ts0 := [T]) (Scope.dec declFoo)
    (by intro T' h; rw [one h]; exact hk) rfl (.cons hs .nil)

theorem kY : Kind d2 dY (tv "Y") := Kind.wfVar (T := obj) (.head _)
theorem sY : Sub d2 dY (tv "Y") obj := Sub.subVar (.head _) .subRefl
theorem kX : Kind d2 dX (tv "X") := Kind.wfVar (T := obj) (.head _)
theorem sA : Sub d2 [] tA obj := Sub.subInherit (D := decA) declA rfl .subRefl

theorem typA2 (Delta : Bounds) (g : Gamma) : Typing d2 Delta g vA tA :=
  Typing.newTop (D := decA) (es1 := []) (es2 := []) declA (kA _) rfl .nil Typing.newObject

theorem typB2 (Delta : Bounds) (g : Gamma) : Typing d2 Delta g vB tB :=
  Typing.newTop (D := decB) (es1 := []) (es2 := []) declB (kB _) rfl .nil Typing.newObject

theorem okObject : ClassOk d2 decObject :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kObj _) (And.intro (by intro M h; cases h) (overrideObj _ _)))

theorem okA : ClassOk d2 decA :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kObj _) (And.intro (by intro M h; cases h) (overrideObj _ _)))

theorem okB : ClassOk d2 decB :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kObj _)
      (And.intro
        (by
          intro M h
          rw [one h]
          exact MethodOk.methodOk (by intro T h; cases h) (by intro T h; rw [one h]; exact kB _) (typB2 _ _))
        (overrideObj _ _)))

theorem okFoo : ClassOk d2 decFoo :=
  And.intro (by intro T h; rw [one h]; exact kObj _)
    (And.intro (by intro T h; rw [one h]; exact kObj _)
      (And.intro
        (by
          intro M h
          rw [one h]
          exact MethodOk.methodOk (by intro T h; cases h) (by intro T h; rw [one h]; exact kX)
            (Typing.call (Delta0 := decFoo.bounds) (Ts2 := [tv "X"]) (Delta1 := []) (T0 := tv "X") (ps := [])
              (body := .call thisE [] (mn "x") []) (Ts' := [])
              (Typing.var rfl) (Scope.dec declFoo)
              (Exists.intro (.dec decFoo) (And.intro declFoo (And.intro rfl (.head _)))) rfl rfl rfl
              (by intro T h; cases h) .nil .nil))
        (overrideObj _ _)))

def gMk : Gamma := [{ T := .cls (cn "Maker") [], x := this }, par (tv "Y") "y"]

theorem consistentMyFoo : Consistent d2 myFooK :=
  Exists.intro [.funnel (tn "Y")] (Exists.intro [tv "Y"] (Exists.intro [] (Exists.intro [myFooMethod]
    (And.intro myFooDeclared (And.intro rfl (And.intro rfl (And.intro (fun _ => Iff.rfl)
      (by
        intro M h
        rw [one h]
        exact OverrideOkM.loc (Delta'' := []) (T0 := tv "Y") (ps := []) (e := ev "y")
          myFooDeclared (.head _) rfl rfl rfl rfl))))))))

theorem kMyFooY : Kind d2 dY (.cls (cn "MyFoo") [tv "Y"]) :=
  Kind.wfClass (Delta0 := dY) (Ts0 := [tv "Y"])
    (Scope.loc (C := cn "Maker") (Delta' := dY) (T0 := tFoo (tv "Y")) (m := mn "mk") (ps := [par (tv "Y") "y"])
      (e := myFooBody) (T := .cls (cn "Maker") []) (Delta := []) (Ts'' := [])
      (Exists.intro (.dec decMaker) (And.intro declMaker (And.intro rfl (.head _))))
      (Exists.intro .hole rfl) (Generic.dec declMaker) (Scope.dec declMaker) (Pairing.funnel (.head _) .nil))
    (by intro T h; rw [one h]; exact kY) rfl (.cons sY .nil)

theorem overrideFoo (Delta : Bounds) (T : Ty) (e : Expr) :
    OverrideOk d2 Delta (tFoo T) [.mk [] T (mn "x") [] e] := by
  intro M C Ts hM hs
  rw [one hM]
  cases subFoo hs rfl with
  | inl h =>
    cases h
    exact OverrideOkM.dec (D := decFoo) (Delta'' := []) (T0 := tv "X") (ps := []) (e := .call thisE [] (mn "x") [])
      declFoo (.head _) rfl rfl rfl rfl
  | inr h => cases h; exact OverrideOkM.absent (D := decObject) declObj (by intro h; cases h)

theorem typMyFoo : Typing d2 dY gMk myFooBody (tFoo (tv "Y")) :=
  Typing.subs
    (Typing.newLocal (Delta' := dY) (Ts'' := [tv "Y"]) consistentMyFoo (Pairing.funnel (.head _) .nil)
      (by intro X h; simp [cod, dY, bnd, obj, Ty.ftvList, Ty.ftv] at h; exact absurd h (fun h => noMem h))
      kMyFooY (kFoo _ _ kY sY)
      (Typing.newTop (D := decFoo) (es1 := []) (es2 := []) declFoo (kFoo _ _ kY sY) rfl .nil Typing.newObject)
      (by
        intro M h
        rw [one h]
        exact MethodOk.methodOk (by intro T h; cases h) (by intro T h; rw [one h]; exact Kind.wfVar (T := obj) (.head _))
          (Typing.var rfl))
      (overrideFoo _ _ _))
    (kFoo _ _ kY sY)
    (Sub.subInheritLocal myFooDeclared rfl .subRefl)

theorem okMaker : ClassOk d2 decMaker :=
  And.intro (by intro T h; cases h)
    (And.intro (by intro T h; rw [one h]; exact kObj _)
      (And.intro
        (by
          intro M h
          rw [one h]
          exact MethodOk.methodOk (by intro T h; rw [one h]; exact kObj _)
            (by
              intro T h
              cases h with
              | head => exact kFoo _ _ kY sY
              | tail _ h => rw [one h]; exact kY)
            typMyFoo)
        (overrideObj _ _)))

theorem declsOk : DeclsOk d2 := by
  intro D h
  have hm : Membership.mem d2 D := h
  simp [d2] at hm
  rcases hm with h | h | h | h | h <;> subst h <;>
    first | exact okObject | exact okA | exact okB | exact okFoo | exact okMaker

def mainMk : Expr := .call (Value.new (cn "Maker") [] []) [tA] (mn "mk") [vA]

theorem typMain : Typing d2 [] [] mainMk (tFoo tA) :=
  Typing.call (Delta0 := []) (Ts2 := []) (Delta1 := dY) (T0 := tFoo (tv "Y")) (ps := [par (tv "Y") "y"])
    (body := myFooBody) (Ts' := [tA])
    (Typing.newTop (D := decMaker) (es1 := []) (es2 := []) declMaker (kMaker _) rfl .nil Typing.newObject)
    (Scope.dec declMaker)
    (Exists.intro (.dec decMaker) (And.intro declMaker (And.intro rfl (.head _)))) rfl rfl rfl
    (by intro T h; rw [one h]; exact kA _) (.cons sA .nil)
    (.cons (typA2 _ _) .nil)

theorem typVLocal : Typing d2 [] [] vLocal (tFoo tA) :=
  Typing.subs
    (Typing.newLocal (Delta' := []) (Ts'' := [])
      (Exists.intro [.funnel (tn "Y")] (Exists.intro [tv "Y"] (Exists.intro [] (Exists.intro [myFooMethod]
        (And.intro myFooDeclared (And.intro rfl (And.intro rfl (And.intro (fun _ => Iff.rfl)
          (by
            intro M h
            rw [one h]
            exact OverrideOkM.loc (Delta'' := []) (T0 := tv "Y") (ps := []) (e := ev "y")
              myFooDeclared (.head _) rfl rfl rfl rfl)))))))))
      (Pairing.ground .nil)
      (by intro X h; cases h)
      (Kind.wfClass (Delta0 := dY) (Ts0 := [tA])
        (Scope.loc (C := cn "Maker") (Delta' := dY) (T0 := tFoo (tv "Y")) (m := mn "mk") (ps := [par (tv "Y") "y"])
          (e := myFooBody) (T := .cls (cn "Maker") []) (Delta := []) (Ts'' := [])
          (Exists.intro (.dec decMaker) (And.intro declMaker (And.intro rfl (.head _))))
          (Exists.intro .hole rfl) (Generic.dec declMaker) (Scope.dec declMaker) (Pairing.funnel (.head _) .nil))
        (by intro T h; rw [one h]; exact kA _) rfl (.cons sA .nil))
      (kFoo _ _ (kA _) sA)
      (Typing.newTop (D := decFoo) (es1 := []) (es2 := []) declFoo (kFoo _ _ (kA _) sA) rfl .nil Typing.newObject)
      (by
        intro M h
        rw [one h]
        exact MethodOk.methodOk (by intro T h; cases h) (by intro T h; rw [one h]; exact kA _) (typA2 _ _))
      (overrideFoo _ _ _))
    (kFoo _ _ (kA _) sA)
    (Sub.subInheritLocal myFooDeclared rfl .subRefl)

end OkD2

-- M1: the class Maker is Ok.
theorem m1 : ClassOk d2 decMaker := OkD2.okMaker

-- V1: the hypotheses of typeSoundness hold together on d1 and the expression of T1.
theorem v1 : WFDecls d1 /\ DeclsOk d1 /\ WFExpr (.field (Value.new (cn "Box") [gA] [vA]) (fn "val")) /\
    Typing d1 [] [] (.field (Value.new (cn "Box") [gA] [vA]) (fn "val")) tA :=
  And.intro w1 (And.intro OkD1.declsOk (And.intro (by decide) t1))

-- V2: the hypotheses of typeSoundness hold together on d2, with the funnelled local class MyFoo,
-- and new Maker<>().<A<>>mk(new A<>()) : Foo<A<>>.
theorem v2 : WFDecls d2 /\ DeclsOk d2 /\ WFExpr OkD2.mainMk /\ Typing d2 [] [] OkD2.mainMk (tFoo tA) :=
  And.intro w5 (And.intro OkD2.declsOk (And.intro (by decide) OkD2.typMain))

-- V3: the result of R7, a copy of MyFoo in the main expression, has type Foo<A<>>.
theorem v3 : Typing d2 [] [] vLocal (tFoo tA) := OkD2.typVLocal

def capL (y : VarName) : Expr :=
  .newLocal (cn "L") [] Object [] [] [.mk [] obj (mn "m") [] (.var y)]
def capBefore : Expr := .ifInst vA tA (vn "x") (capL (vn "x")) vB
def capAfter : Expr := .ifInst vA tA this (capL this) vB

-- W26: Fresh accepts renaming the variable x of an if into this, which the method m of the local class captures;
-- the result violates A8.
theorem w26 : Fresh capBefore capAfter /\ Not (WFExpr capAfter) :=
  And.intro
    (And.intro
      (RenE.ifInst (.new .nil)
        (.newLocal .nil (.cons (.mk (Xs' := []) (xs' := []) rfl rfl .var) .nil)) (.new .nil))
      (RenE.ifInst (.new .nil)
        (.newLocal .nil (.cons (.mk (Xs' := []) (xs' := []) rfl rfl .var) .nil)) (.new .nil)))
    (by decide)

end Funnelling.Examples
