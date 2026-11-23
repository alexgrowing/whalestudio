import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdjoinRootLinearEquivOfCharpolyEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n) (A : Matrix (Fin n) (Fin n) E), A.charpoly = P.1 → ∃ φ : Fld P ≃ₗ[E] (Fin n → E), ∀ y, A *ᵥ φ y = φ (alpha P * y) := by
  first | exact @GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | exact GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | (intros; apply GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly <;> assumption)
