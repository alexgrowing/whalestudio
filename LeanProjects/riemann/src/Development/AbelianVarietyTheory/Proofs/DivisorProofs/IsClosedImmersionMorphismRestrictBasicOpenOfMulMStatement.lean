import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionMorphismRestrictBasicOpenOfMulM
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) → ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) → IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  first | exact @GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range | exact GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range | (intros; apply GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range <;> assumption)
