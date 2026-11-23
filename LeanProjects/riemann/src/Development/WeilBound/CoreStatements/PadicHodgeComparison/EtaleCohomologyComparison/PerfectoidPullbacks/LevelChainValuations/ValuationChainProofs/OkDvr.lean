import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

theorem ok_dvr_pf [FiniteDimensional ℚ_[l] K] : IsDomain (OK l K) ∧ IsDiscreteValuationRing (OK l K) ∧
    ∀ a : OK l K, a ≠ 0 → ∃ k : ℕ, a ∣ (l : OK l K) ^ k := by
  have := OK_dvr (l := l) (K := K)
  refine ⟨inferInstance, OK_dvr, ?_⟩
  intro a ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hlm : ((l : ℕ) : OK l K) ∈ IsLocalRing.maximalIdeal (OK l K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff]
    have e : (((((l : ℕ) : OK l K) : K)) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one.ne
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hlm
  refine ⟨n, ?_⟩
  have h1 : a ∣ ϖ ^ n := ⟨(↑u⁻¹ : OK l K), by rw [hu, mul_comm (u : OK l K), mul_assoc, Units.mul_inv, mul_one]⟩
  exact h1.trans (pow_dvd_pow_of_dvd hlm n)

end CrystallineSemistableComparison.Pb.Kap
