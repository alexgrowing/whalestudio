import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_and_finite_app_of_isFinite : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) → IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  first | exact @GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict | exact GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict | (intros; apply GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict <;> assumption)
