import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AI

open MeasureTheory

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev S2 := Metric.sphere (0 : E3) 1

noncomputable def sphereMeasure : Measure S2 :=
  ((volume : Measure E3).toSphere Set.univ)⁻¹ • (volume : Measure E3).toSphere

noncomputable def gPoly (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X 1 * ∑ j ∈ Finset.range (2 * k),
    (-1 : ℝ) ^ j • (MvPolynomial.X 0 ^ (2 * k - 1 - j) * MvPolynomial.X 1 ^ j)

noncomputable def dgPoly (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (gPoly k))

noncomputable def kappa (k : ℕ) : ℝ :=
  -∫ n₁ : S2, ∫ n₂ : S2, (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (n₁ : E3) (n₂ : E3)) / 2) *
      MvPolynomial.eval ![(n₁ : E3) 2, (n₂ : E3) 2] (dgPoly k) ∂sphereMeasure ∂sphereMeasure

def Kappa1Statement : Prop := kappa 1 = 1 / 2

def Kappa2Statement : Prop := kappa 2 = 2 / 3

def SphereInvStatement : Prop :=
  IsProbabilityMeasure sphereMeasure ∧
  ∀ L : E3 ≃ₗᵢ[ℝ] E3,
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2)) sphereMeasure sphereMeasure

def ArchimedesStatement : Prop :=
  ∀ (u v w : E3) (f : ℝ → ℝ), ‖u‖ = 1 → IntervalIntegrable f volume (-1) 1 →
    Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure = (1 / 2) * ∫ t in (-1 : ℝ)..1, f t) ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v ∂sphereMeasure =
      (1 / 2) * ∫ t in (-1 : ℝ)..1, f t * t * inner ℝ u v) ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w ∂sphereMeasure =
      (1 / 2) * ∫ t in (-1 : ℝ)..1, f t * (t ^ 2 * (inner ℝ u v * inner ℝ u w) +
        (1 - t ^ 2) / 2 * (inner ℝ v w - inner ℝ u v * inner ℝ u w)))

end ReciprocityTheory.ChartRestriction.G.AI
