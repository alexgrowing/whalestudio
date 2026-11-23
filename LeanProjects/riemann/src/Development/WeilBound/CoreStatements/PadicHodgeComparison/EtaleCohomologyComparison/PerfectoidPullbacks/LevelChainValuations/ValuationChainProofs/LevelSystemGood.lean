import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.unitB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CgBasis
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CgLift
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.QbLePf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)

theorem level_system_good [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (U : Cov M.q) (hU : ∀ α, U.d α + m ≤ s) (hs : m ≤ s)
    (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
    (hr : ∀ n j x, trM (QA L M s) none (l : L.A) n j (rH (n + 1) j x) = rH n j ((M.HS false j).r n x)) :
    (chainOf hL M s (qb_le_pf hL M s) rH).Good where
  unit := unit_B_pf (l := l) hL
  fin j := (m_fin M hM j).1
  basis j _ bs w := cg_basis_pf hL M hM s U hU j bs w
  r_tr n j x := hr n j x
  red_tr n j z := trM_redM (QA L M s) none (l : L.A) n j z
  lift j x hx := by
    obtain ⟨e, he⟩ := cg_lift_pf hL M hM s hs j
    obtain ⟨z, hz⟩ := he.1 (fun n => rH n j (x n)) (fun n => by
      exact (hr n j (x (n + 1))).trans (congrArg (rH n j) (hx n)))
    exact ⟨e, z, hz⟩
  sep j z hz := by
    obtain ⟨e, he⟩ := cg_lift_pf hL M hM s hs j
    have h0 := he.2.1 z hz
    have h1 : (chainOf hL M s (qb_le_pf hL M s) rH).b j (((l : L.A) ^ e) • z) = 0 := by
      rw [h0, map_zero]
    rw [LinearMap.map_smulₛₗ] at h1
    have hu : IsUnit ((L.ι ((l : L.A) ^ e)) : L.B) := by
      rw [map_pow, map_natCast]
      exact (unit_B_pf hL).pow e
    exact hu.smul_left_cancel.1 (by rw [smul_zero]; exact h1)

end

end CrystallineSemistableComparison.Pb.Kap
