import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.unitB

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

theorem qb_le_pf {L : Lev R m} (hL : L.Good) (M : Model l K) (s : ℕ) :
    ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T) := by
  intro T hT
  obtain ⟨⟨h1, h2⟩, V, hV, hU⟩ := hT
  have hu : IsUnit ((l : ℕ) : T.B) := by
    have := (unit_B_pf (R := R) hL).map T.i
    simpa using this
  obtain ⟨u, hu'⟩ := hu
  refine ⟨⟨h1, fun r (x : T.B) hx => ?_⟩, ⊤, Set.mem_singleton _, ?_⟩
  · change ((l : ℕ) : T.B) * x ∈ T.pdPow r at hx
    change x ∈ T.pdPow r
    have e : x = ((u⁻¹ : T.Bˣ) : T.B) * ((l : T.B) * x) := by
      rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact Ideal.mul_mem_left _ _ hx
  · intro x _
    exact Set.mem_univ _

end CrystallineSemistableComparison.Pb.Kap
