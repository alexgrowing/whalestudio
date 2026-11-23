import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AntisymmetrizeBlockVandermondeOf
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem pderiv_blockPowerSum_apply (d : IndexData) (k : ℕ) (σ τ : Fin d.f) (i : Fin d.N) :
    pderiv (τ, i) (RestTerms.blockPowerSum d.f d.N k σ : XPoly d) =
      if σ = τ then (k : XPoly d) * X (τ, i) ^ (k - 1) else 0 := by
  classical
  rw [RestTerms.blockPowerSum, map_sum]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro l _ hl
      rw [pderiv_pow, pderiv_X_of_ne (show (σ, l) ≠ (σ, i) by simp [hl]), mul_zero]
    · simp
  · refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [pderiv_pow, pderiv_X_of_ne (show (σ, l) ≠ (τ, i) by simp [h]), mul_zero]

theorem intFl_blockPowerSum_mul (d : IndexData) (k : ℕ) (σ : Fin d.f) (G : XPoly d)
    (hk1 : 1 ≤ k) (hkN : k ≤ d.N) :
    intFl d (RestTerms.blockPowerSum d.f d.N k σ * G) = 0 := by
  simp only [intFl, LinearMap.smul_apply, flagIntegralLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [RestTerms.FlagIntegralKillsPowerSums.intersectionNumber_baseChange d.f d.N k σ G hk1 hkN, smul_zero]

theorem intFl_natCast_mul (d : IndexData) (n : ℕ) (G : XPoly d) :
    intFl d ((n : XPoly d) * G) = n * intFl d G := by
  rw [show (n : XPoly d) = C (n : ℚ) from (map_natCast C n).symm, C_mul', map_smul, smul_eq_mul]

theorem ShFormula.proof : ShFormula.Statement := by
  classical
  intro d τ F Q _ _ hQ
  have hinner : ∀ k : ℕ,
      ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j),
          ∑ σ : Fin d.f, pderiv (τ, i) (RestTerms.blockPowerSum d.f d.N k σ * Q k σ) =
        ∑ σ : Fin d.f, RestTerms.blockPowerSum d.f d.N k σ *
            ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) (Q k σ) +
          (k : XPoly d) * lowerPowerSum d (k - 1) τ * Q k τ := by
    intro k
    simp_rw [pderiv_mul, pderiv_blockPowerSum_apply, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq' univ τ, if_pos (Finset.mem_univ τ)]
    rw [add_comm, Finset.sum_comm]
    congr 1
    · simp_rw [Finset.mul_sum]
    · rw [lowerPowerSum, Finset.mul_sum, Finset.sum_mul]
  have hexp : ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) F =
      ∑ k ∈ Icc 1 d.N, (∑ σ : Fin d.f, RestTerms.blockPowerSum d.f d.N k σ *
            ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) (Q k σ) +
          (k : XPoly d) * lowerPowerSum d (k - 1) τ * Q k τ) := by
    rw [hQ]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hinner k)
  unfold shiftFl
  rw [hexp, map_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Icc] at hk
  rw [map_add, map_sum,
    Finset.sum_eq_zero (fun σ _ => intFl_blockPowerSum_mul d k σ _ hk.1 hk.2), zero_add, mul_assoc,
    intFl_natCast_mul]

theorem ShFormula.full : ShFormula.Statement := ShFormula.proof

end GroundTheory.Heights₂.Heights.TheoremB
