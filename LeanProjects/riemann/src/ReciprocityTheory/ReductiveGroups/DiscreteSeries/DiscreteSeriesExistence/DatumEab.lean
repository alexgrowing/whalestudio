import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem eab_cpart1_eq (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart1 ε Z = S7.cpart1 ε Z := rfl

theorem eab_cpart2_eq (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart2 ε Z = S7.cpart2 ε Z := rfl

theorem eab_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    S7.cpart1 ε Z + Complex.I • S7.cpart2 ε Z = Z := by
  unfold S7.cpart1 S7.cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = (1 / 2 : ℂ) by field_simp]
  rw [← smul_add]
  rw [show Z - Jm ε * Zᴴ * Jm ε + (Z + Jm ε * Zᴴ * Jm ε) = (2 : ℂ) • Z by rw [two_smul]; abel]
  rw [smul_smul]; norm_num

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

end ReciprocityTheory.ChartRestriction.DS
