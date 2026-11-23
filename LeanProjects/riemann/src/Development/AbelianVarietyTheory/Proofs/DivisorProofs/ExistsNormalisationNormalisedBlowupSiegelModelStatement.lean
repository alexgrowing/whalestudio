import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationNormalisedBlowupSiegelModel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisation_normalisedBlowup_siegelModel : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z), (∀ x ∈ J.support, x ∉ Set.range i) → IsNormBl π J → ∀ X₁ : Setup F W i, ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ X₁.M.Z) (ν : S₁ ⟶ S), IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ IsFinite ν ∧ ν ≫ π = p₁ ≫ X₁.π ∧ IsIso (p₁ ∣_ (X₁.π ⁻¹ᵁ i.opensRange)) ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ X₁.π)) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (b : Sp R ⟶ X₁.M.Z), a ≫ π = b ≫ X₁.π → Set.range (jK R ≫ b ≫ X₁.π) ⊆ Set.range i → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ ν = a ∧ ξ₁ ≫ p₁ = b := by
  first | exact @GlobalTheory.PoincCov.exists_normalisation_cover | exact GlobalTheory.PoincCov.exists_normalisation_cover | (intros; apply GlobalTheory.PoincCov.exists_normalisation_cover <;> assumption)
