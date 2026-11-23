import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaConstant_mul_of_coprime_ellipticPolynomials : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (P₁ P₂ : E[X]), P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ → kap (P₁ * P₂) = kap P₁ * kap P₂ ∧ (∃ δ : GL (Fin a) E, (δ * thE E a δ).val.charpoly = P₁) ∧ P₁ * P₂ ∈ Ell E (a + b) := by
  first | exact @GlobalTheory.BCT.KapMul.kap_mul | exact GlobalTheory.BCT.KapMul.kap_mul | (intros; apply GlobalTheory.BCT.KapMul.kap_mul <;> assumption)
