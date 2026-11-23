import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.RgExh.Dec.N.S

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S

def Fub2 : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∃ (μN μM : Measure (Formalism.REAL.UJ ε)), SFinite μN ∧ SFinite μM ∧ μM (flagM ε (W A))ᶜ = 0 ∧
      (∀ a : Formalism.REAL.UJ ε, a ∈ flagM ε (W A) → (∀ m ∈ flagM ε (W A), m * a = a * m) → μM.map (· * a) = μM) ∧
      (∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
        (∀ g, ∀ k ∈ Formalism.REAL.KG ε, F (g * k) = F g) →
        ∫⁻ g, F g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN) ∧
      ∀ ν : Measure (PSub ε A), ν.IsHaarMeasure → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
          ∫⁻ x, F x ∂(muPar ε A ν) = c * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN

end CompanionTheory.RgExh.Dec.N.S
