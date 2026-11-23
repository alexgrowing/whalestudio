import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BeIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.JToSetting

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down

open ReciprocityTheory.ChartRestriction.DS.Mult1 Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
  ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

variable {k r : ℕ}

section twist

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mat k r → (H →L[ℂ] H)} {t : Mat k r}

theorem tw_cancel (ht : t ∈ GV k r) (g : Mat k r) : t * (t⁻¹ * g * t) * t⁻¹ = g := by
  simp only [Matrix.mul_assoc]
  rw [gv_mul_inv ht, Matrix.mul_one, ← Matrix.mul_assoc, gv_mul_inv ht, Matrix.one_mul]

theorem tw_irr (hσ : Formalism.MainNotions.S.IsIrredOn (GV k r) σ) (ht : t ∈ GV k r) :
    Formalism.MainNotions.S.IsIrredOn (GV k r) (fun g => σ (t * g * t⁻¹)) := by
  intro S hS hst
  refine hσ S hS fun g hg v hv => ?_
  have := hst (t⁻¹ * g * t) (gv_mul (gv_mul (gv_inv ht) hg) ht) v hv
  simpa only [tw_cancel ht] using this

end twist

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down
