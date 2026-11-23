import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem depth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l →
    LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧
      ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  intro D L P l hl
  obtain ⟨j, hj, hjL⟩ := P.Lw_j l hl
  have hne : ({j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} : Set ℕ).Nonempty := ⟨j, hj⟩
  have hmem : LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l := Nat.sInf_mem hne
  have hle : depth L l ≤ j := Nat.sInf_le hj
  refine ⟨hmem, by omega, fun hlt => ?_⟩
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  by_contra hc
  push_neg at hc
  interval_cases h : depth L l
  · simp at hmem
    linarith
  · simp at hmem
    linarith

end GlobalTheory
