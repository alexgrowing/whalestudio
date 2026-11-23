import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselSmoothSectionLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hensel_smooth_section_lift : ∀ (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ (U : Over (Sp R₁)), Smooth U.hom → ∀ x₀ : Sp R ⟶ U.left, x₀ ≫ U.hom = spMap π → ∃ x : Sp R₁ ⟶ U.left, x ≫ U.hom = 𝟙 _ ∧ spMap π ≫ x = x₀ := by
  first | exact @GlobalTheory.QuotLift.exists_section_lift | exact GlobalTheory.QuotLift.exists_section_lift | (intros; apply GlobalTheory.QuotLift.exists_section_lift <;> assumption)
