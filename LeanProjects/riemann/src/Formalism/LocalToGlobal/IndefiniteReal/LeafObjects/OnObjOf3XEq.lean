import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.MirabolicInclusion
import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.FunObj
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.Obj

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Sb3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) := (R.toCx3 F).data F.cr false

abbrev xAt3 (F : Face3 D A3) (R : RealDat3 D A3 Ks) : ℝ := (F.fc (R.toCx3 F).zs).Z.x

def onObjOf3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : OnConst) (I : OnIn R.toRealDat) :
    OnObj (Sb3 R F) (OnP R.toRealDat) c :=
  onMk R.toRealDat F.lv2 (Sb3 R F) (Equiv.refl _)
    (fun j => Fintype.linearCombination D.what₂.LL (R.toRealDat.bL F.lv2 false j)) (xAt3 F R) c I

abbrev baseDefiniteSide (R : RealDat3 D A3 Ks) (F : Face3 D A3) : DefSide A3.fam3.base3 := Formalism.IndefR.Cx.lv (F.fc (R.toCx3 F).zs) false

abbrev FunIn3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Type 1 := FunInD D (baseDefiniteSide R F)

def funObjOf3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (J : FunIn3 R F) : FunData D.what₂.LL (baseDefiniteSide R F) :=
  funMk D (baseDefiniteSide R F) J

section Ties

variable (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : OnConst) (I : OnIn R.toRealDat)

end Ties

section Depth

open Formalism.L2.Pj

def OnIn.withDepth {A' : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A' Ks} (I : OnIn R) (Tc : CoreJ D) (Dd : DepData D.host.E)
    [NumberField.IsCMField D.host.E] [StarRing (𝓞 D.host.E)]
    [Algebra (𝓞 Tc.Q.c.F) (𝓞 D.what₂.LL)] [Algebra.IsIntegral (𝓞 Tc.Q.c.F) (𝓞 D.what₂.LL)]
    [Algebra (𝓞 D.host.E) D.what₂.LL] : OnIn R :=
  { I with
    E := fun v j => EAt (H := Tc.Q.H) (Dw := Tc.Q.Dw ((j : ℕ) + 1)) (l := Tc.Q.l) (Xo := Tc.Q.Xo ((j : ℕ) + 1)) (c := Tc.Q.c)
      Dd v ((j : ℕ) + 1)
    σ := fun _ j => sigAt (H := Tc.Q.H) (Dw := Tc.Q.Dw ((j : ℕ) + 1)) Dd ((j : ℕ) + 1)
    nnK := fun j => nnKAt (H := Tc.Q.H) Dd ((j : ℕ) + 1) }

variable (Tc : CoreJ D) (Dd : DepData D.host.E)
    [NumberField.IsCMField D.host.E] [StarRing (𝓞 D.host.E)]
    [Algebra (𝓞 Tc.Q.c.F) (𝓞 D.what₂.LL)] [Algebra.IsIntegral (𝓞 Tc.Q.c.F) (𝓞 D.what₂.LL)]
    [Algebra (𝓞 D.host.E) D.what₂.LL]

include Tc Dd

def levelObjectWithDepth (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : OnConst) (I : OnIn R.toRealDat) :
    OnObj (Sb3 R F) (OnP R.toRealDat) c :=
  onObjOf3 R F c (I.withDepth Tc Dd)

end Depth

end Formalism.IndefR.Obj
