import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MorphismExtensionFromGenericPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_extension_from_generic_point : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] [IsLocalRing R]
    (φ : A →+* R), φ.Flat → IsLocalHom φ → ∀ (γ : FractionRing A →+* FractionRing R),
    (∀ a, γ (algebraMap A _ a) = algebraMap R _ (φ a)) → ∀ (Y : Scheme.{0})
    (ψ₀ : Sp (FractionRing A) ⟶ Y) (χ : Sp R ⟶ Y), jK R ≫ χ = spMap γ ≫ ψ₀ →
    ∃ ψ : Sp A ⟶ Y, jK A ≫ ψ = ψ₀ ∧ spMap φ ≫ ψ = χ := by
  first | exact @GlobalTheory.extension_descends_of_flat | exact GlobalTheory.extension_descends_of_flat | (intros; apply GlobalTheory.extension_descends_of_flat <;> assumption)
