import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportional
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (g₁ g₂ : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ) (b₁ b₂ q : R), GlobalTheory.PsiRing.Coef D χ u th g₁ b₁ → GlobalTheory.PsiRing.Coef D χ u th g₂ b₂ → b₁ = q * b₂ → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q g₁ g₂ := by
  first | exact @GlobalTheory.PsiRing.secIsMul_of_coef | exact GlobalTheory.PsiRing.secIsMul_of_coef | (intros; apply GlobalTheory.PsiRing.secIsMul_of_coef <;> assumption)
