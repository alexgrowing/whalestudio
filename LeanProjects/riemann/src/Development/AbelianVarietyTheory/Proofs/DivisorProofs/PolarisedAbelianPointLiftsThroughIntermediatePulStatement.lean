import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPointLiftsThroughIntermediatePul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianPoint_lifts_through_intermediate_pullback : ∀ {S₀ S₁ S₂ : Scheme.{0}} (f₁ : S₁ ⟶ S₀) (f₂ : S₂ ⟶ S₁) (A : PolAV S₀) (B : PolAV S₁) (P : PolAV S₂) (b : B.A.left ⟶ A.A.left) (a : P.A.left ⟶ A.A.left), IsGrpPullback B.A A.A f₁ b → IsGrpPullback P.A A.A (f₂ ≫ f₁) a → ∃ c : P.A.left ⟶ B.A.left, c ≫ b = a ∧ c ≫ B.A.hom = P.A.hom ≫ f₂ ∧ IsGrpPullback P.A B.A f₂ c ∧ (LBIso P.L (A.L.pull a) → LBIso B.L (A.L.pull b) → LBIso P.L (B.L.pull c)) := by
  first | exact @GlobalTheory.PolLift.lift_of_pullback_comp | exact GlobalTheory.PolLift.lift_of_pullback_comp | (intros; apply GlobalTheory.PolLift.lift_of_pullback_comp <;> assumption)
