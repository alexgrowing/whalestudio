import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundNefPlusAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_lowerBound_nef_plus_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c n : ℕ) (α : ℝ), 0 < n → NefFib P.L → P.L.SemiPos D → IsAmpleLB P.A.B → P.A.SemiPos D → ((P.L.pow n).tens P.A).IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (α / (D + 1).factorial / (n : ℝ) ^ (D + 1) - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M ((M / n : ℕ) - c) 1 := by
  first | exact @GlobalTheory.HSNef.lowerBound_along_div | exact GlobalTheory.HSNef.lowerBound_along_div | (intros; apply GlobalTheory.HSNef.lowerBound_along_div <;> assumption)
