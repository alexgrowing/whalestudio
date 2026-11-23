import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowDegreePos.proof : ChowDegreePos.Statement := by
  intro n k δ W g hk hW hg hδ
  by_contra hlt
  have hδ0 : δ = 0 := by omega
  subst hδ0

  have hnt : NonTorsionWeight (groupWeight k n) := by
    intro m ij h
    have := congrFun h ij.1
    simpa [groupWeight] using this

  have hsupp : ∀ m ∈ g.support, m = 0 := by
    intro m hm
    have h1 : Finsupp.weight (groupWeight k n) m = 0 := hδ (mem_support_iff.1 hm)
    ext ij
    exact (weightedDegree_eq_zero_iff hnt).1 h1 ij
  obtain ⟨c, rfl⟩ : ∃ c, g = C c := by
    refine ⟨coeff 0 g, ?_⟩
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [hm]
    · by_contra hne
      exact hm (hsupp m (mem_support_iff.2 hne)).symm
  have hc : c ≠ 0 := by
    intro h
    apply hg.1
    rw [h, C_0]
  have hdvd : (C c : MvPolynomial (Fin k × Fin n) ℂ) ∣ 1 :=
    ⟨C c⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hvan := (hg.2 1).2 hdvd

  obtain ⟨x, hx0, hx⟩ : ∃ x : Fin n → AlgebraicClosure ℂ, x ≠ 0 ∧ ∀ p ∈ W, aeval x p = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hW.isRelevant
    apply hj
    have hrad : X j ∈ W.radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℂ)]
      rw [mem_vanishingIdeal_iff]
      intro y hy
      by_cases hy0 : y = 0
      · subst hy0
        simp
      · exact absurd ⟨y, hy0, hy⟩ hne
    rwa [hW.isPrime.radical] at hrad
  have hmem : (0 : Fin k × Fin n → AlgebraicClosure ℂ) ∈ incidence W k :=
    ⟨x, hx0, hx, fun i => by simp⟩
  have := hvan 0 hmem
  simp at this

end GroundTheory.Heights₂.Heights
