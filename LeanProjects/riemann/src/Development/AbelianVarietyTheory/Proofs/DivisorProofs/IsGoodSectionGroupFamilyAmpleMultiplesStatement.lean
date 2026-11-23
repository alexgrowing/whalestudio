import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodSectionGroupFamilyAmpleMultiples
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodSectionGroupFamily_ampleMultiples : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → GoodFam P D (gdeg P.L D / D.factorial) fun m => P.H m 1 := by
  first | exact @GlobalTheory.HSAmp.GoodH.goodFam_H | exact GlobalTheory.HSAmp.GoodH.goodFam_H | (intros; apply GlobalTheory.HSAmp.GoodH.goodFam_H <;> assumption)
