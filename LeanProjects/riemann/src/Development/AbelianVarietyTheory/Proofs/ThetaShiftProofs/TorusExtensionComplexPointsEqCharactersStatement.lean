import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtensionComplexPointsEqCharacters
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_complexPoints_eq_characters : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g : ℕ) (u : HolUnif D.P.A D.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ct : D.X →+ (Fin g → ℂ)), u.IsAH Hm χ → u.IsRig D.rig → (∀ x, u.ex (ct x) = D.c x) → ∀ z : Fin g → ℂ, (∀ lam : D.X →+ ℂ, ∃! p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left ∧ ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x)) ∧ ∀ p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left → ∃ lam : D.X →+ ℂ, ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x) := by
  first | exact @GlobalTheory.TorusExtChar.points_eq_characters | exact GlobalTheory.TorusExtChar.points_eq_characters | (intros; apply GlobalTheory.TorusExtChar.points_eq_characters <;> assumption)
