import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjLinear_isometry_compact_unitary_type_weyl_module : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (u : Fin k → ℝ), (∀ i : Fin k, u i = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), IsHCTypeU k u π → ∃ j : W →ₗ⋆[ℂ] MvPolynomial (Fin n × Fin n) ℂ, (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ ξ η, normFock lam (j η) (j ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (π (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  first | exact @GlobalTheory.WeylConjType.exists_conj_weyl | exact GlobalTheory.WeylConjType.exists_conj_weyl | (intros; apply GlobalTheory.WeylConjType.exists_conj_weyl <;> assumption)
