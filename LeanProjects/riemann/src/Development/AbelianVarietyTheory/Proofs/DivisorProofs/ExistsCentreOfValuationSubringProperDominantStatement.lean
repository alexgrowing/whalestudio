import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentreOfValuationSubringProperDominant
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centre_of_valuationSubring_proper_dominant : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsProper s]
    (V : ValuationSubring Y.functionField) (x : X), (∀ f, RegAt x f → functionFieldMap s f ∈ V) →
    ∃ y : Y, s y ⤳ x ∧ ∀ f, RegAt y f → f ∈ V := by
  first | exact @GlobalTheory.ProperCentre.exists_regAt_centre | exact GlobalTheory.ProperCentre.exists_regAt_centre | (intros; apply GlobalTheory.ProperCentre.exists_regAt_centre <;> assumption)
