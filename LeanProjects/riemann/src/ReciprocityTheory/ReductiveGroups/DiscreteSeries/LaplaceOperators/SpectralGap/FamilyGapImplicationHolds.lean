import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapBigLap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.DSUniv

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS
open scoped Matrix InnerProductSpace

theorem bridge_inv_mul (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : P⁻¹ * P = 1 := by
  have hu : IsUnit P := hP.1.1
  exact Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hu)

theorem bridge_conj (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * g * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε ∧ P⁻¹ * (P * g * P⁻¹) * P = g := by
  have hPi : P⁻¹ * P = 1 := bridge_inv_mul k r ε P hP
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have e1 : Pᴴ * P = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this
  have e2 : P * Pᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have hc : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  refine ⟨?_, ?_⟩
  · show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
    rw [hinv]
    calc (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ)
        = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = P * Pᴴ * Formalism.REAL.Jm ε * (P * Pᴴ) := by
          rw [hc, hg', ← hc]; simp [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [e2]; simp
  · calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp [Matrix.mul_assoc]
      _ = g := by rw [hPi]; simp

end ReciprocityTheory.ChartRestriction.DS.Lap
