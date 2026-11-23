import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.OnObjOf3XEq
import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.LatticeFramesAtBaseLevel

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.Obj

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def faceLiftPage (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat)
    (hd : NeZero D.host.d) : SlopeBoundParameters :=
  slopeParametersAtScale (xAt3 F R) I J hd

def faceLiftFactor (R : RealDat3 D A3 Ks) (F : Face3 D A3) (I : OnIn R.toRealDat) (J : SlopeArithmeticParameters R.toRealDat) (hd : NeZero D.host.d)
    (i : Fin D.R.m) : SlopeBoundLiftData D.what₂.LL (faceLiftPage R F I J hd) :=
  liftSlopeDataAtScale R.toRealDat (xAt3 F R) I J hd i

def faceFrameMatrix (R : RealDat3 D A3 Ks) (F : Face3 D A3) (J : SlopeArithmeticParameters R.toRealDat) (i : Fin D.R.m) :
    InfinitePlace D.what₂.LL → Matrix (Fin ((Sb3 R F).dW i)) (Fin ((Sb3 R F).dW i)) ℂ :=
  volumeScaledLatticeFrames (Sb3 R F) (Equiv.refl _) J i

end Formalism.IndefR.Obj
