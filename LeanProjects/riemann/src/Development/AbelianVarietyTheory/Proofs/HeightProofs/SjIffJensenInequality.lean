import Mathlib
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SphereBlockLogMean

open MeasureTheory NumberField MvPolynomial

noncomputable section

namespace GlobalTheory.HeightZeroCompare

open ReciprocityTheory.MultiplicativeHeights GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

theorem gaussAbs_eq {K : Type} [Field K] [NumberField K] {ι : Type} (w : FinitePlace K)
    (f : MvPolynomial ι K) : gaussAbs w f = gaussAbsValue w f := rfl

def JensenInequality : Prop :=
  ∀ (N a : ℕ) (f : MvPolynomial (Fin (N + 1)) ℂ) (u : EuclideanSpace ℂ (Fin (N + 1))),
    f.IsHomogeneous a → ‖u‖ = 1 → eval (fun j => u j) f ≠ 0 →
    Integrable (sphereLogAbs f) (sphereMeasure N) ∧
      Real.log ‖eval (fun j => u j) f‖ - (a : ℝ) / 2 * (harmonic N : ℝ) ≤ sphereLogMean f

def conjVec {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j => starRingEnd ℂ (u j)

def BlockIntegrable : Prop :=
  ∀ (B N : ℕ) (a : Fin B → ℕ) (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ), P ≠ 0 →
    IsBlockHomogeneous P a → Integrable (blockLogAbs P) (blockSphereMeasure B N)

end GlobalTheory.HeightZeroCompare
