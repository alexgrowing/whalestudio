import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LieIdentityArcWitnessIff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_identity_arc_witness_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.LieId W ν v ↔ (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsTanGt ν ∧ LieImg W ν v) := by
  first | exact @GlobalTheory.LieIdImg.lieId_iff | exact GlobalTheory.LieIdImg.lieId_iff | (intros; apply GlobalTheory.LieIdImg.lieId_iff <;> assumption)
