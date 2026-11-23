import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smith_normal_form_integral_matrix : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ (P P' : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L) (a : Fin n' → ℕ),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ Q * Q' = 1 ∧
      ∀ i j, (P * x * Q - Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.smith_int_approx | exact GlobalTheory.Hk3.smith_int_approx | (intros; apply GlobalTheory.Hk3.smith_int_approx <;> assumption)
