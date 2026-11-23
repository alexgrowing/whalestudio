import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FlatW

theorem eq_zero_of_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] (m : ℕ) {x : Acris l}
    (h : (l : Acris l) ^ m * x = 0) : x = 0 := by
  induction m with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply ACris.eq_zero_of_p_mul_eq_zero (K := ℂ_[l]) (p := l)
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem flat_AW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) :
    Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro a ha
  obtain ⟨⟨y, hy0⟩, hy⟩ := (Submodule.mem_torsion_iff _).1 ha
  have hne : y ≠ 0 := nonZeroDivisors.ne_zero hy0
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' y hne
  have hu : IsUnit (r.w (b : WittVector l r.k)) := b.isUnit.map r.w
  have key : ∀ x : Acris l, r.w y * x = 0 → x = 0 := by
    intro x h
    rw [e, map_mul, map_pow, map_natCast] at h
    apply eq_zero_of_pow_mul_eq_zero m
    apply hu.mul_right_eq_zero.1
    linear_combination h
  exact (Submodule.mem_bot _).2 (key a hy)

end GlobalTheory.CompanionTheory.FlatW
