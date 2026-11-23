import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialEigenvalueCongruenceVanishes
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_eigenvalue_congruence_vanishes : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (E : Type) [Field E] [Algebra ℤ_[l] E], Function.Injective (algebraMap ℤ_[l] E) → ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ p ∈ abelian₂ X l E, p.2 ∈ Triv E w Γ → p.1 = 0 := by
  first | exact @GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv | exact GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv | (intros; apply GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv <;> assumption)
