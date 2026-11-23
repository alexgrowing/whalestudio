import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSectionsModBaseIdealOfClosedImmersion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_sections_mod_baseIdeal_of_closedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ (V : Z.Opens) (hV : IsAffineOpen V), IsAffineOpen (φ ⁻¹ᵁ V) → Function.Surjective ((Ideal.Quotient.mk (((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom)).comp (φ.app V).hom) := by
  first | exact @GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion | exact GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion | (intros; apply GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion <;> assumption)
