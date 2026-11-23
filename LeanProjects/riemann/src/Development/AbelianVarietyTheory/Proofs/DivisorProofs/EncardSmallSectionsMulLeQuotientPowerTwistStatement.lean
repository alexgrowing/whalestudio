import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsMulLeQuotientPowerTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_small_sections_mul_le_quotient_power_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, ∀ (N m : ℕ), (P.Bl N (m - c) 1).encard * (P.Bl 0 (b * N - c) 1).encard ≤ {f | f ∈ P.H N (-c) ∧ f * s ^ m ∈ P.Bl N (m - c) 2}.encard * (P.Bl 0 (b * N + m - c) 2).encard := by
  first | exact @GlobalTheory.HSNef.encard_mul_le_at_level_twist | exact GlobalTheory.HSNef.encard_mul_le_at_level_twist | (intros; apply GlobalTheory.HSNef.encard_mul_le_at_level_twist <;> assumption)
