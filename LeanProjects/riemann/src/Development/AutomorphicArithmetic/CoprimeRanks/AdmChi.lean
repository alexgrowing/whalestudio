import Development.AutomorphicArithmetic.CharacterBoxes.Imports
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC HostParam.Seam GlobalTheory.EX

theorem admissible_ranks_of_CMDatum (R : Ranks) (H0 : HostAx R.toFrame) : admitted R H0 := fun _ c h hq => exists_host R H0 h hq c

theorem admissibleClassesTwistedChar : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (φ : Frame) (H0 : HostAx φ),
    s.eps = eps → x0 ≤ s.x → s.x ^ (2 + 8 * s.eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) →
    ∃ (R : Ranks) (h : R.toFrame = φ), RankVal s R ∧ admitted R (h ▸ H0) := by
  intro eps heps heps'
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_ranks_rankVal_frame eps heps heps'
  refine ⟨x0, fun s φ H0 hs hx hlo hup => ?_⟩
  obtain ⟨R, h, hRV⟩ := hx0 s hs hx φ hlo hup
  exact ⟨R, h, hRV, admissible_ranks_of_CMDatum R _⟩

end UpperTheory.Top

end
