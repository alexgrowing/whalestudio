import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanSelfIntersectionNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithKleiman_selfIntersection_nonneg : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → (∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h → ∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (C : HermLB p) (c : ℝ), C.IsNef D → C.IsSelfInter c → 0 ≤ c := by
  first | exact @GlobalTheory.KleimanStep.selfInter_nonneg | exact GlobalTheory.KleimanStep.selfInter_nonneg | (intros; apply GlobalTheory.KleimanStep.selfInter_nonneg <;> assumption)
