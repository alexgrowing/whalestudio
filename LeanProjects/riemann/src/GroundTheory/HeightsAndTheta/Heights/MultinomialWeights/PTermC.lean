import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeHomogeneous
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

theorem flagNormalisation_ne_zero (f N : ℕ) : flagNormalisation f N ≠ 0 := by
  unfold flagNormalisation
  refine div_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ?_)
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

theorem flagIntegral_blockVandermonde_pos (f N : ℕ) :
    0 < RestTerms.flagIntegral f N (RestTerms.blockVandermonde f N) := by
  unfold RestTerms.flagIntegral
  have hne : (RestTerms.blockVandermonde f N).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact RestTerms.Flag.blockVandermonde_ne_zero f N
  refine Finset.sum_pos (fun α hα => ?_) hne
  have hc : coeff α (RestTerms.blockVandermonde f N) ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  refine mul_pos (mul_self_pos.mpr hc) ?_
  exact Finset.prod_pos fun i _ => by dsimp only; exact_mod_cast Nat.factorial_pos _

theorem exists_intFl_eq_one (d : IndexData) :
    ∃ Q : XPoly d, Q.IsHomogeneous d.D ∧ intFl d Q = 1 := by
  set Δ : XPoly d := RestTerms.blockVandermonde d.f d.N
  have hΔ : Δ.IsHomogeneous d.D := RestTerms.FlagVandermondeHomogeneous.proof d.f d.N
  have hval : intFl d Δ = flagNormalisation d.f d.N * RestTerms.flagIntegral d.f d.N Δ := rfl
  have hc : intFl d Δ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (flagNormalisation_ne_zero _ _)
      (flagIntegral_blockVandermonde_pos d.f d.N).ne'
  refine ⟨(intFl d Δ)⁻¹ • Δ, ?_, ?_⟩
  · have hm : Δ ∈ homogeneousSubmodule (Idx d) ℚ d.D := (mem_homogeneousSubmodule _ _).mpr hΔ
    exact (mem_homogeneousSubmodule _ _).mp (Submodule.smul_mem _ _ hm)
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]

theorem TermC.proof (h₁ : HeightLimitIdentity.Statement) : TermC.Statement := by
  intro d S h82 hfl B0 A0 b0 hA hb hF
  obtain ⟨Q, hQ, hQ1⟩ := exists_intFl_eq_one d
  have e := h₁ d S h82 hfl B0 A0 b0 hA hb (tau0 S) Q hQ hQ1
  have hv : S.vol ≠ 0 := S.vol_pos.ne'
  have hval : (d.j : ℝ) * A0 + (d.N : ℝ) * b0 = -S.hB B0 := by
    rw [e, hF.1 (tau0 S) Q hQ, hQ1]
    field_simp
    push_cast
    ring
  rw [hval, abs_neg]
  exact hF.2

end GroundTheory.Heights₂.Heights.TheoremB
