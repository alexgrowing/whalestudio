import Mathlib
import Development.AutomorphicSpectrum.ParallelStatements.FiniteSums.BesselPeriodFreeData
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicFormsHyp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv Formalism.IndefR.Mi
  Formalism.IndefR.Mult MeasureTheory Matrix GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.BesselPeriodFreeData
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SepInhab

def IsOrthogonalSlopeTestFamily (D : D7) (u : D.what₂.Word) (j : ℕ) (A : SlopeTestRemainingChoices (D.sp.Y j)) : Prop :=
  IsAuxiliaryHeckeCharacter (D.sp.Y j) j (D.mem u).A.T A ∧
    ∀ l, (∀ i < rho D j, hF (D.sp.Y j) (fun r => frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j) r l) (A.e i) = 0 ∧
        hF (D.sp.Y j) (fun r => frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j) r l) (A.ev i) = 0) ∧
      (HasZ D j → hF (D.sp.Y j) (fun r => frameMat (D.sp.Y j) (D.sp.X j) (D.sp.iXY j) r l) A.z = 0)

end GlobalTheory.CompanionTheory.SepInhab

end
