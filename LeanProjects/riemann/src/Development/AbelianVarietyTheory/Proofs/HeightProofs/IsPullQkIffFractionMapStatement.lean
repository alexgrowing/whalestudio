import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsPullQkIffFractionMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullQk_iff_fraction_map : ∀ (A A' : Type) [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] (g : A →+* A') (D₀ : Out.DegPre A) (D₁ : Out.DegPre A') (pd : Out.IsPullDeg g D₀ D₁), D₀.TauBimult → ∀ (k : ℕ) (p : Out.QkPt D₀ (FractionRing A) k) (q : Out.QkPt D₁ (FractionRing A') k), GlobalTheory.ArcPull.IsPullQk pd p q ↔ ∃ hg : Function.Injective g, pd.xe q.y = p.y ∧ q.g.b.left ≫ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.prOf pd = spMap (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg) ≫ p.g.b.left ∧ ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.GenThrough pd.w Out.DegPre.gtε (q.g.s x) (p.g.s (pd.xe x)) (spMap (GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.fracMap g hg)) := by
  first | exact @GlobalTheory.QkPullDirect.isPullQk_iff | exact GlobalTheory.QkPullDirect.isPullQk_iff | (intros; apply GlobalTheory.QkPullDirect.isPullQk_iff <;> assumption)
