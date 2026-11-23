import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable

noncomputable section

open NumberField

namespace Ad3.K

def Explicit (D : Dat) (L : GP.Loc D) : Prop :=
  (∀ v : Pl, L.VF v = LFS.VF (GP.psiF v) (V2 (GP.psiF v) (D.ν v) (D.ν v)⁻¹)) ∧
    L.VR = Submodule.span ℂ (Set.range (LR.sec D.k))

variable (K : Type) [Field K] [NumberField K]

def QuadraticBaseChangeGL3Statement : Prop :=
  Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (D : Dat) (L : GP.Loc D), Explicit D L → ∀ hV : WhA (GP.VA L),
    QOut D (GP.VA L) hV → ∃ DK : DatK K, DK.k = D.k ∧ BCOf D DK ∧ AnK DK

end Ad3.K
