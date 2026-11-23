import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinitePointExtendsSection
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_point_extends_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → ∀ t, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U → ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, (∀ z, σ.left z ∈ U) ∧ toUnit (genPt R) ≫ σ = Γ.pt t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point | exact GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point <;> assumption)
