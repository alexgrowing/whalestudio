import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPower

namespace GlobalTheory.PMonE

theorem glOnto_zero_and_glCount_zero : GLOnto 0 ∧ GLCount 0 := by
  constructor
  · intro F _ _ _ _ p _ _ m _ _ e D he _ M hM b hb
    obtain ⟨x, hx, -⟩ := existsUnique_integral_gsum_eq F p m e D he M
      (fun i j => by simp [hM.top]) (fun n hn i j => hM.small n (by omega) i j) b hb
    exact ⟨x, hx⟩
  · intro F _ _ _ _ p _ _ m _ _ e D he _ M hM _
    obtain ⟨y, hy, huniq⟩ := existsUnique_integral_gsum_eq F p m e D he M
      (fun i j => by simp [hM.top]) (fun n hn i j => hM.small n (by omega) i j) 0 (fun i => by simp)
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_exists]
    exact ⟨⟨y, hy⟩, fun z => Subtype.ext (huniq z.1 z.2)⟩

end GlobalTheory.PMonE
