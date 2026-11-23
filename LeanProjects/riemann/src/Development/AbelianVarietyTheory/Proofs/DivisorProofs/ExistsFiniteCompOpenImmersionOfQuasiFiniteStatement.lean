import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompOpenImmersionOfQuasiFinite
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite : ∀ (U X : Scheme.{0}) (f : U ⟶ X), IsNoetherian X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f → ∃ (T : Scheme.{0}) (q : T ⟶ X) (j : U ⟶ T), IsFinite q ∧ IsOpenImmersion j ∧ j ≫ q = f := by
  first | exact @GlobalTheory.ZMTFin.exists_finite_openImmersion | exact GlobalTheory.ZMTFin.exists_finite_openImmersion | (intros; apply GlobalTheory.ZMTFin.exists_finite_openImmersion <;> assumption)
