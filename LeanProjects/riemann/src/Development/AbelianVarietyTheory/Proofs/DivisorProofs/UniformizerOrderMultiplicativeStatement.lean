import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOrderMultiplicative
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_order_multiplicative : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsDedekindDomain Γ(X, ⊤)] (z : X)
    (P : Ideal Γ(X, ⊤)) (π a : Γ(X, ⊤)) (n : ℕ), P.IsPrime → P ≠ ⊥ → GlobalTheory.SteinFibre.under z = P → π ∈ P →
    π ∉ P ^ 2 → a ∈ P ^ n → a ∉ P ^ (n + 1) →
      Scheme.ord (algebraMap Γ(X, ⊤) X.functionField a) z =
        n * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField π) z := by
  first | exact @GlobalTheory.SteinFibre.ord_eq_mul_ord_uniformizer | exact GlobalTheory.SteinFibre.ord_eq_mul_ord_uniformizer | (intros; apply GlobalTheory.SteinFibre.ord_eq_mul_ord_uniformizer <;> assumption)
