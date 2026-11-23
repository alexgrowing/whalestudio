import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliser
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_centralizer_regular_twistedCentraliser : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r → regular₂ G γ → IsNrm G r γ δ z → (Subgroup.centralizer {γ}).map (carry G r z) = GlobalTheory.BCT.twCent (sigG G r) δ := by
  first | (exact @GlobalTheory.CarryCent.map_centralizer_carry) | (exact GlobalTheory.CarryCent.map_centralizer_carry) | (intros; apply GlobalTheory.CarryCent.map_centralizer_carry  <;> assumption)
