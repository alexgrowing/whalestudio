import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndepA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CayleyIndependent

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS
open Matrix

theorem cayleyIndep : CayleyIndepStatement := by
  intro k r ε lam H _ _ _ σ P₀ P h0 h1 hDS
  set σ₁ : Mat k r → (H →L[ℂ] H) := fun g => σ (P₀⁻¹ * g * P₀) with hσ₁
  have e0 : star P₀ * P₀ = 1 := Matrix.mem_unitaryGroup_iff'.mp h0.2
  have e0' : P₀ * star P₀ = 1 := Matrix.mem_unitaryGroup_iff.mp h0.2
  have e1 : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp h1.2
  have e1' : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp h1.2
  have hinv0 : P₀⁻¹ = star P₀ := Matrix.inv_eq_left_inv e0
  have hinv1 : P⁻¹ = star P := Matrix.inv_eq_left_inv e1
  have hH0 := h0.1.2
  have hH1 := h1.1.2
  have hJ : star P₀ * Formalism.REAL.Jm ε * P₀ = star P * Formalism.REAL.Jm ε * P := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hH0, hH1]
  have hbK : P₀ * star P ∈ Formalism.REAL.Kset ε := by
    refine ⟨Submonoid.mul_mem _ h0.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e1)), ?_⟩
    calc P₀ * star P * Formalism.REAL.Jm ε = P₀ * (star P * Formalism.REAL.Jm ε * P) * star P := by
          rw [Matrix.mul_assoc P₀ _ (star P), Matrix.mul_assoc (star P * _) P (star P), e1', Matrix.mul_one,
            Matrix.mul_assoc]
      _ = P₀ * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P := by rw [hJ]
      _ = Formalism.REAL.Jm ε * (P₀ * star P) := by
          simp only [← Matrix.mul_assoc]
          rw [e0', Matrix.one_mul]
  have haK : P * star P₀ ∈ Formalism.REAL.Kset ε := by
    refine ⟨Submonoid.mul_mem _ h1.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e0)), ?_⟩
    calc P * star P₀ * Formalism.REAL.Jm ε = P * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P₀ := by
          rw [Matrix.mul_assoc P _ (star P₀), Matrix.mul_assoc (star P₀ * _) P₀ (star P₀), e0', Matrix.mul_one,
            Matrix.mul_assoc]
      _ = P * (star P * Formalism.REAL.Jm ε * P) * star P₀ := by rw [hJ]
      _ = Formalism.REAL.Jm ε * (P * star P₀) := by
          simp only [← Matrix.mul_assoc]
          rw [e1', Matrix.one_mul]
  have hbU := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj hbK
  have haU := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj haK
  have hab : P * star P₀ * (P₀ * star P) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star P₀), e0, Matrix.one_mul, e1']
  have hba : P₀ * star P * (P * star P₀) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star P), e1, Matrix.one_mul, e0']
  have hfun : (fun g => σ (P⁻¹ * g * P)) = fun g => σ₁ (P₀ * star P * g * (P * star P₀)) := by
    funext g
    rw [hσ₁]
    congr 1
    rw [hinv0, hinv1]
    simp only [← Matrix.mul_assoc]
    rw [e0, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [e0, Matrix.mul_one]
  obtain ⟨hc, hnt, hU, hI, hS, ⟨S0, hS0⟩, hmin⟩ := hDS
  rw [hfun]
  refine ⟨⟨hc, hnt, ?_, ?_, ?_, ⟨S0, ?_⟩, fun μ S hS' => hmin μ S ?_⟩, ?_⟩
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.urep_conj
    all_goals first | assumption | exact hU
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.irred_conj (hirr := hI)
    all_goals first | assumption | exact hU
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.sqint_conj (hsq := hS)
    all_goals first | assumption | exact hU
  · rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]
    · exact hS0
    all_goals first | assumption | exact hU
  · rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff] at hS'
    · exact hS'
    all_goals first | assumption | exact hU
  · unfold Formalism.MainNotions.S.lowKSub
    refine congrArg sSup (Set.ext fun S => ?_)
    simp only [Set.mem_setOf_eq]
    rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]
    all_goals first | assumption | exact hU

end ReciprocityTheory.ChartRestriction.DS.Lap
