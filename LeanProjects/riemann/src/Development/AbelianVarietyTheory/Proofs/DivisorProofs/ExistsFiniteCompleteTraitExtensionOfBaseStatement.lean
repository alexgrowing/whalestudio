import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteTraitExtensionOfBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrExtensionQkPointsRational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_complete_trait_extension_of_base : ∀ (R W R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (ρ : R →+* R₁), FinExt ρ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra (FractionRing W) Ω] [Algebra.IsAlgebraic (FractionRing W) Ω] (e : FractionRing R₁ →+* Ω), (∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) (φ r))) → ∃ (W₁ : Type) (_ : CommRing W₁) (_ : IsDomain W₁) (_ : IsLocalRing W₁) (iw : W →+* W₁) (φ₁ : R₁ →+* W₁) (σ : Ω →+* AlgebraicClosure (FractionRing W₁)), GlobalTheory.LN.CDvr W₁ ∧ Function.Injective iw ∧ iw.Finite ∧ IsLocalHom iw ∧ Function.Injective φ₁ ∧ IsLocalHom φ₁ ∧ φ₁.comp ρ = iw.comp φ ∧ (∀ w, σ (algebraMap (FractionRing W) Ω (algebraMap W (FractionRing W) w)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (iw w))) ∧ ∀ r, σ (e (algebraMap R₁ (FractionRing R₁) r)) = algebraMap (FractionRing W₁) (AlgebraicClosure (FractionRing W₁)) (algebraMap W₁ (FractionRing W₁) (φ₁ r)) := by
  first | exact @GlobalTheory.TraitExt.exists_finite_trait_extension | exact GlobalTheory.TraitExt.exists_finite_trait_extension | (intros; apply GlobalTheory.TraitExt.exists_finite_trait_extension <;> assumption)
