import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationBlowupPullbackFiniteCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisation_blowup_pullback_finiteCover : ∀ {o : CommRingCat.{0}} [Algebra.FiniteType ℤ o] {Z Z' M : Scheme.{0}} (z : Z ⟶ Spec o) [LocallyOfFiniteType z] (b : Z' ⟶ Z) [IsProper b] (J : Z.IdealSheafData), FinalTheorems.Blowup b J → ∀ [IsIntegral M] [GlobalTheory.IsNormalScheme M] (U : Z.Opens) (g' : M ⟶ U.toScheme) [IsFinite g'], (∃ m, (g' ≫ U.ι) m ∉ J.support) → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (ν₁ : S₁ ⟶ (b ⁻¹ᵁ U).toScheme), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsFinite ν₁ ∧ ν₁ ≫ (b ∣_ U) = p₁ ≫ g' ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g' ≫ U.ι)) ∧ (∀ m, (g' ≫ U.ι) m ∉ J.support → m ∈ Set.range p₁) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (a : Sp R ⟶ (b ⁻¹ᵁ U).toScheme) (β : Sp R ⟶ M), a ≫ (b ∣_ U) = β ≫ g' → (∀ w, (jK R ≫ β ≫ g' ≫ U.ι) w ∉ J.support) → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ ν₁ = a ∧ ξ₁ ≫ p₁ = β := by
  first | exact @GlobalTheory.USep.exists_normalisation_pullback_cover | exact GlobalTheory.USep.exists_normalisation_pullback_cover | (intros; apply GlobalTheory.USep.exists_normalisation_pullback_cover <;> assumption)
