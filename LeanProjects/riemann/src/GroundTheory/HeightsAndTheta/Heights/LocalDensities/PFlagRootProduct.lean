import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

theorem FlagRootProduct.rootPairing_eq_abs {N p : ℕ} {lam : Fin N → ℝ}
    (hd : IsSplitDominant N p lam) (q : LowerPair N) :
    rootPairing N p lam q = |lam q.1.1 - lam q.1.2| := by
  obtain ⟨⟨a, b⟩, hba⟩ := q
  have hba' : b.val < a.val := hba
  have ha := a.isLt
  have hb := b.isLt
  unfold rootPairing
  dsimp only
  by_cases h : b.val < p ∧ p ≤ a.val
  · rw [if_pos h]
    have hle : lam b ≤ lam a := hd a b (by
      unfold splitRank
      rw [if_pos h.2, if_neg (by omega)]
      omega)
    rw [abs_of_nonneg (by linarith)]
  · rw [if_neg h]
    have hle : lam a ≤ lam b := hd b a (by
      unfold splitRank
      split_ifs <;> omega)
    rw [abs_of_nonpos (by linarith)]
    ring

theorem FlagRootProduct.proof : FlagRootProduct.Statement := by
  intro N p lam hd
  have h := fun q => FlagRootProduct.rootPairing_eq_abs (N := N) (p := p) hd q
  exact ⟨h, Finset.prod_congr rfl fun q _ => h q⟩

end GroundTheory.Heights₂.Heights.FourB
