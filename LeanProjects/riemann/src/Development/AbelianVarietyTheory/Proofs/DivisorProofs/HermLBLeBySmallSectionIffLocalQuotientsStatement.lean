import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotients
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ (r : A.B.ι → X.functionFieldˣ) (r' : B.B.ι → X.functionFieldˣ), IsRatSec A.B r ∧ IsRatSec B.B r' ∧ (∀ (x : X) i j, x ∈ A.B.U i → x ∈ B.B.U j → RegAt x ((r i : X.functionField) / (r' j : X.functionField))) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (A.B.U i) → y ∈ ptsIn p σ (B.B.U j) → ‖ratVal ((r i : X.functionField) / (r' j : X.functionField)) y‖ * Real.exp (-((A.φ σ).φ i y - (B.φ σ).φ j y) / 2) ≤ 1 := by
  first | exact @GlobalTheory.HSNef.le_iff_local | exact GlobalTheory.HSNef.le_iff_local | (intros; apply GlobalTheory.HSNef.le_iff_local <;> assumption)
