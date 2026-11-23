import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsAcyclicOfTwoSectionsRetraction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction : ∀ (C : Type 1) [Category.{0} C] (M : Coef C) (S : C ⥤ C) (u v : 𝟭 C ⟶ S) (r : ∀ T, M.obj (S.obj T) →+ M.obj T), (∀ (T T' : C) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x)) → (∀ T x, r T (M.map (u.app T) x) = 0) → (∀ T x, r T (M.map (v.app T) x) = x) → M.Ac0 ∧ M.Ac1 ∧ M.Ac2 := by
  first | exact @GlobalTheory.coef_acyclic_of_two_sections | exact GlobalTheory.coef_acyclic_of_two_sections | (intros; apply GlobalTheory.coef_acyclic_of_two_sections <;> assumption)
