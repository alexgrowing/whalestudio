import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnPreimageIntegralOfFiniteModelMap
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOn_preimage_integral_of_finite_model_map : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ U : M₁.Z.Opens, IsAffineOpen U → (U : Set M₁.Z).Nonempty → ∀ b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z), ∃ f : Polynomial Ω₁, f.Monic ∧ (∀ i, f.coeff i ∈ M₁.ringOn (U : Set M₁.Z)) ∧ Polynomial.eval₂ (algebraMap Ω₁ Ω₂) b f = 0 := by
  first | exact @GlobalTheory.Poinc.finite_preimage_integral | exact GlobalTheory.Poinc.finite_preimage_integral | (intros; apply GlobalTheory.Poinc.finite_preimage_integral <;> assumption)
