import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodHermPair_adapted_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L N : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField) (c : ℕ), P.L = L ∧ P.Good D b s t ∧ GenAt P c ∧ Regime P D ∧ Le ((P.A.pow c).dual) N := by
  first | exact @GlobalTheory.HSNef.exists_good_pair_twist | exact GlobalTheory.HSNef.exists_good_pair_twist | (intros; apply GlobalTheory.HSNef.exists_good_pair_twist <;> assumption)
