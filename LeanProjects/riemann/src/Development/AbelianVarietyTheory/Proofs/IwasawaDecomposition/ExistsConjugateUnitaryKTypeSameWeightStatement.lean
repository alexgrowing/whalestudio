import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeight
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_unitaryKType_sameWeight : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : FiniteDimensional ℂ E) (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (J : H →ₛₗ[starRingEnd ℂ] E), Function.Bijective J ∧ IsURepOn (UJset (allPos k)) π ∧ IsKTypeOf (allPos k) π Λ ⊤ ∧ ∀ g u, π g (J u) = J (σ (g.map star) u) := by
  first | exact @GlobalTheory.ConjugateType.exists_conjugate_type | exact GlobalTheory.ConjugateType.exists_conjugate_type | (intros; apply GlobalTheory.ConjugateType.exists_conjugate_type <;> assumption)
