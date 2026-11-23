import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharpolyUnitaryEqConjugateReciprocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_unitary_eq_conjugateReciprocal : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 → ∀ γ : GRat σ J, γ.1.1.charpoly = sharp σ n γ.1.1.charpoly := by
  first | exact @GlobalTheory.TrEll.charpoly_eq_sharp | exact GlobalTheory.TrEll.charpoly_eq_sharp | (intros; apply GlobalTheory.TrEll.charpoly_eq_sharp <;> assumption)
