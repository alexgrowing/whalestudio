import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PrCloudAddPrNode
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom.Inh

variable {k r : ℕ}

@[reducible] def uniqueIdxZero : Unique (Idx k r 0) :=
  ⟨⟨⟨∅, rfl⟩⟩, fun I => Subtype.ext (Finset.card_eq_zero.1 I.2)⟩

attribute [local instance] uniqueIdxZero

def detPow (n : ℕ) (m : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ →L[ℂ] ℂ :=
  (g.det ^ m) • ContinuousLinearMap.id ℂ ℂ

def lamDet (n : ℕ) (m : ℤ) : Fin n → ℝ := fun a => (m : ℝ) + Formalism.QuantumDeterminants.rhoStd n a

def z0 (k : ℕ) : Fin (2 * 0 + k + 1) → ℂ := bvec (wI k 0 (Fin.last k))

def posW (k : ℕ) (i : Fin k) : Fin (2 * 0 + k + 1) := ⟨i.val, by omega⟩

def piDet (k : ℕ) (m : ℤ) (g : Mat k 0) : ℂ →L[ℂ] ℂ :=
  detPow k m (g.submatrix (posW k) (posW k))

def lamN (N : ℕ) : Fin (2 * 0 + 1 + 1) → ℝ := ![-(N : ℝ) - 1 / 2, -(2 * N : ℝ) - 1 / 2]

end GlobalTheory.Mom.Inh
