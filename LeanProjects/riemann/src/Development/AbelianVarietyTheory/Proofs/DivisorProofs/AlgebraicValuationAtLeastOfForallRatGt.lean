import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_of_forall_rat_gt : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    ∀ (r : ℝ) (x : ℂ), (∀ q : ℚ, r < q → Sz l lam q x) → Sz l lam r x := by
  intro l hl lam r x h
  obtain ⟨q₀, hq₀⟩ := exists_rat_gt r
  obtain ⟨hx, -⟩ := h q₀ hq₀
  refine ⟨hx, ?_⟩
  by_contra hc
  rw [not_le] at hc
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := lt_trans one_pos hl1
  have ht : 0 < ‖lam ⟨x, hx⟩‖ := lt_trans (Real.rpow_pos_of_pos hl0 r) hc
  have h1 : r < Real.logb l ‖lam ⟨x, hx⟩‖ := (Real.lt_logb_iff_rpow_lt hl1 ht).2 hc
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  obtain ⟨_, hle⟩ := h q hq1
  exact absurd ((Real.lt_logb_iff_rpow_lt hl1 ht).1 hq2) (not_lt.2 hle)

end GlobalTheory.QFam
