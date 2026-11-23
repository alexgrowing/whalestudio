import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalingIntegralRescale
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_scaling_integral_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → ∀ c : D.X → (FractionRing R)ˣ, (∀ χ : D.X, ∃ u : Rˣ, c χ * a χ = Units.map (algebraMap R (FractionRing R)).toMonoidHom u) → Nonempty (PsiOn (GlobalTheory.PolDeg.rescale D c) ⊤) := by
  first | exact @GlobalTheory.PsiTopUnit.exists_psiOn_top_rescale | exact GlobalTheory.PsiTopUnit.exists_psiOn_top_rescale | (intros; apply GlobalTheory.PsiTopUnit.exists_psiOn_top_rescale <;> assumption)
