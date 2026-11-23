import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackSectionIntegralValueDualPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackSection_integralValue_dualPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ) (β : D.toPre.X) (σ : D.toPre.SecB k β) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) σF (D.toPre.famφB β) (DegPre.famε k) σ (DegPre.prB D.toPre C).left 1 → ∀ (Q : Sp (DualNumber V) ⟶ D.toPre.P.A.left), Q ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) → ∀ (r : Sp (DualNumber C) ⟶ (DegPre.BF D.toPre C).left), r ≫ (DegPre.prB D.toPre C).left = spMap (dualMap (toF V C)) ≫ Q → ‖(sE σF r ν.J).fst‖ ≤ 1 ∧ ‖(sE σF r ν.J).snd‖ ≤ 1 := by
  first | exact @GlobalTheory.IntGaugePull.sE_norm_le_one_of_pull | exact GlobalTheory.IntGaugePull.sE_norm_le_one_of_pull | (intros; apply GlobalTheory.IntGaugePull.sE_norm_le_one_of_pull <;> assumption)
