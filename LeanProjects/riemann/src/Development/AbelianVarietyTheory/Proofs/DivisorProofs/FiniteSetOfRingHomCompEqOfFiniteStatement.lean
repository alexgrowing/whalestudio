import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfRingHomCompEqOfFinite
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_ringHom_comp_eq_of_finite' : ∀ (A Ω K : Type) [CommRing A] [CommRing Ω] [Field K] (φ : A →+* Ω) (ρ : A →+* K), φ.Finite → Set.Finite {τ : Ω →+* K | τ.comp φ = ρ} := by
  first | exact @GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite | exact GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite | (intros; apply GlobalTheory.finite_setOf_ringHom_comp_eq_of_finite <;> assumption)
