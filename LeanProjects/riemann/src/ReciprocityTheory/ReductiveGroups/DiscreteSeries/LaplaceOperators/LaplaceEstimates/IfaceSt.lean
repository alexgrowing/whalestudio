import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement
import Formalism.RealPlaceAnalysis.SmoothVectorGrowthBound

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def frob {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖g i j‖ ^ 2)

def DecDerivStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    S7.IsHCParam lam → GapAtLeast ε lam h → hNeed ε < h → 1 ≤ S7.q0 ε → S7.IsMu lam μ →
    ∀ (w : List (Fin n × Fin n)) (v₁ v₂ : T.V), ∃ C : ℝ, ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε w (fun y => ⟪v₂, S7.PsiM T μ y v₁⟫_ℂ) g‖ ≤
        C * frob g ^ (-(h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))))

end ReciprocityTheory.ChartRestriction.DS.Lap
