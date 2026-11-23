import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge
open scoped Classical

def expR {n : ℕ} (ε : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : Formalism.REAL.UJ ε :=
  if h : Formalism.REAL.inUJ ε (NormedSpace.exp (unrealify x)) then ⟨(Matrix.isUnit_exp (unrealify x)).unit, h⟩ else 1

def ExpProdU : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))),
    m ⊔ h = gLie ε → (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    GaugeDens ε → ∃ r : ℝ, 0 < r ∧ ∃ D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt D 0 ∧ D 0 = gaugeU ε ∧ Measurable D ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        Formalism.REAL.muG ε ((fun p => expR ε (L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) *
          expR ε (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' A) =
        ∫⁻ p in A, ENNReal.ofReal (D p)

end PI.AprimeInfW
