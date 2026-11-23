import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.WeightNormalizerAndExponentsOfWeightSum
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nnW_eq_pow_mul_and_c2_cHalf_le_of_weight_sum : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (wL wF w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) → (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) → nnW B hinj EX w = nnW B hinj EX wL ^ k * nnW B hinj EX wF ∧ c2 D w ≤ k * c2 D wL + c2 D wF ∧ Formalism.MainNotions.DIV.Cons.cHalf w ≤ k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF := by
  first | exact @GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum | exact GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum | (intros; apply GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum <;> assumption)
