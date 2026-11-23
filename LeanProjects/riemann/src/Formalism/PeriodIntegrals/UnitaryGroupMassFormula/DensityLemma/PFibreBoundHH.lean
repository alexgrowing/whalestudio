import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundH
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def UnipotentSetIsClosedSubgroup : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → B2.IsClosedSubgroup (C2.N0set k r z)

def NuConc : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → nuZ k r z (C2.N0set k r z)ᶜ = 0

def NuLeft : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z →
    ∀ a ∈ C2.N0set k r z, (nuZ k r z).map (lmulM a) = nuZ k r z

def NuFin : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z →
    ∀ K : Set (Mt k r), IsCompact K → nuZ k r z K < ∞

def NuNeZero : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → nuZ k r z ≠ 0

end PI.UnitaryGroupMassFormula.DLm
