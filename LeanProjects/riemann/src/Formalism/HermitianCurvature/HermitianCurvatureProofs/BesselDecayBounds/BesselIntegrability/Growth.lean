import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.GrowthW

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def hsN {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j))

theorem hsN_nonneg {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hsN g :=
  Real.sqrt_nonneg _

def GrowthG : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Mt k r)) (A : ℝ), Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r) μG → Formalism.FourierDecayAlt.B.AB k r ≤ A →
    (∫⁻ g : Mt k r, ENNReal.ofReal (hsN (Matrix.of g) ^ (-A)) ∂μG) < ∞

def UWBound : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ C : ℝ, ∀ h ∈ UWset k r z, hsN h ≤ C

def SUpper {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Prop := ∀ i j : Fin m, j ≤ i → X i j = 0

def LieNUpper : Prop := ∀ (k r : ℕ) (X : Formalism.FourierDecayAlt.B.Mat k r), PI.WUN.InLieN k r X → SUpper X

def ExpUpper : Prop :=
  ∀ m : ℕ, 0 < m → ∃ C D : ℝ, 0 < D ∧ ∀ X : Matrix (Fin m) (Fin m) ℂ, SUpper X →
    1 + hsN X ≤ C * hsN (NormedSpace.exp X) ^ D

def GrowthS : Prop :=
  ∀ k r : ℕ, ∃ A0 : ℝ, 0 ≤ A0 ∧ ∀ (z : Fin (2 * r + k + 1) → ℂ) (μW : Measure (Mt k r)) (κN : ℝ≥0∞) (A : ℝ),
    inWb k r z → 0 < Tz k r z → μW {x | Matrix.of x ∉ UWset k r z} = 0 → IsFiniteMeasure μW → κN ≠ ∞ → A0 < A →
    (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (hsN (Matrix.of p.1 * Matrix.of p.2) ^ (-A))
      ∂(μW.prod (haarLie (Nset k r) κN))) < ∞

section Assembly

variable {k r : ℕ}

theorem norm_le_hsN (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    ‖x‖ ≤ hsN (unrealify x) := by
  rw [EuclideanSpace.norm_eq]
  unfold hsN
  apply le_of_eq
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [unrealify, Complex.normSq_mk, Real.norm_eq_abs, sq_abs]
  ring

abbrev EE (k r : ℕ) := EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)

end Assembly

end Formalism.MainNotions.GrowthW
