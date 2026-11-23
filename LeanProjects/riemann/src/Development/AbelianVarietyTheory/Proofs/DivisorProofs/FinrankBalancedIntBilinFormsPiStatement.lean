import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsPi
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_balancedIntBilinForms_pi : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J] [DecidableEq J], Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar (J → 𝓞 E)) = Module.finrank ℚ E * Fintype.card J * Fintype.card J := by
  first | exact @GlobalTheory.BalRank.finrank_balBil_pi | exact GlobalTheory.BalRank.finrank_balBil_pi | (intros; apply GlobalTheory.BalRank.finrank_balBil_pi <;> assumption)
