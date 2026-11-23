import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ T : Finset X.K, (∀ x ∈ T, Lev X M x) ∧ ∀ f : X.K, Lev X M f → f ∈ Submodule.span (IntermediateField.adjoin Ω {X.jK}) (T : Set X.K) := by
  first | exact @GlobalTheory.KZ.ES.LevFin.exists_finset_span | exact GlobalTheory.KZ.ES.LevFin.exists_finset_span | (intros; apply GlobalTheory.KZ.ES.LevFin.exists_finset_span <;> assumption)
