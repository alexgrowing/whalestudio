import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem restPsumIdeal_generators_eq_range (f N : ℕ) :
    {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = RestTerms.blockPowerSum f N k τ} =
      Set.range fun i : Fin N × Fin f => RestTerms.blockPowerSum f N ((i.1 : ℕ) + 1) i.2 := by
  ext P
  constructor
  · rintro ⟨k, τ, hk1, hkN, rfl⟩
    refine ⟨(⟨k - 1, by omega⟩, τ), ?_⟩
    simp only
    congr 1
    omega
  · rintro ⟨i, rfl⟩
    exact ⟨(i.1 : ℕ) + 1, i.2, by omega, by omega, rfl⟩

theorem RestCutIdealSum.proof : RestCutIdealSum.Statement := by
  intro f N A hA
  rw [restPsumIdeal, restPsumIdeal_generators_eq_range, Ideal.mem_span_range_iff_exists_fun] at hA
  obtain ⟨c, hc⟩ := hA
  exact ⟨c, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

end GroundTheory.Heights₂.Heights
