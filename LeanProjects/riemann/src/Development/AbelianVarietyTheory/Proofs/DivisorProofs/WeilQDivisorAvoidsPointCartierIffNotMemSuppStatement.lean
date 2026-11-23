import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (D₀ : CartierDiv X) (m : ℕ) (z : X), D₀.Eff → 0 < m → (Off (qWeil D₀ m) z ↔ z ∉ D₀.supp) := by
  first | exact @GlobalTheory.PairStep.off_qWeil_iff_notMem_supp | exact GlobalTheory.PairStep.off_qWeil_iff_notMem_supp | (intros; apply GlobalTheory.PairStep.off_qWeil_iff_notMem_supp <;> assumption)
