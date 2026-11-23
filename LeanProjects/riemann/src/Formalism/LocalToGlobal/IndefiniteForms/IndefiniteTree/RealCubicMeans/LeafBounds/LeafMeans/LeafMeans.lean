import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.OnObjOf3XEq
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.LeafMeans.LeafMeansFree
import Development.WeilBound.SupplementaryPages.FaceFrameMatrix

noncomputable section

open NumberField IsDedekindDomain Finset
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Links Formalism.IndefR.Obj

namespace Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem leafMeans_iff (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) (Ca Cb : ℝ) (j : Fin D.R.m) :
    LeafMeans Ca Cb (faceLiftFactor R F I J hd j) ↔
      SlopeMeansBounds (J.X j) (J.sl j) (faceLiftFactor R F I J hd j).T (faceLiftPage R F I J hd).LL0 (faceLiftFactor R F I J hd j).U (J.E0 j) (J.cc j) (J.Qcc j) Ca Cb := Iff.rfl

end Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
