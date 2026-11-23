import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentPullbackComplexDualNumbers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionTangent_pullback_complexDualNumbers : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR V)), GtTan gm₀ → ∃ gm : GtPt D (TE V C), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm ∧ (∃ o : GtPtF D C, o.IsZero ∧ GtPt.IsPullF C (redE C) gm o) ∧ (gm₀.b = DegPre.zeroT D (epsR V) → gm.b = DegPre.zeroT D (TE V C)) ∧ ∀ (a : V) (χ : D.X), (∀ (Z : Scheme.{0}) (q : Z ⟶ (epsR V).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm₀.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))) → vE (gm.s χ) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr (toF V C a) := by
  first | exact @GlobalTheory.MBLow.TanPull.main | exact GlobalTheory.MBLow.TanPull.main | (intros; apply GlobalTheory.MBLow.TanPull.main <;> assumption)
