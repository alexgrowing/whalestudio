import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSubsingletonOfClosedImmersionModIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_subsingleton_of_closedImmersion_mod_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ z : Z, I ≤ (p z).asIdeal → (⇑φ ⁻¹' {z}).Subsingleton := by
  first | exact @GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict | exact GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict | (intros; apply GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict <;> assumption)
