import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorialWeightedPairingDetPowProportional
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorialWeightedPairing_detPow_proportional : (∀ (C : Type) [Field C] [CharZero C] (n₀ M Y : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), M ≤ Y → Q.IsHomogeneous (n₀ * M) →
    (∑ A ∈ (cayDet n₀ C ^ Y).support, MvPolynomial.coeff A (cayDet n₀ C ^ Y) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ (Y - M) * Q)) * (∑ A ∈ (cayDet n₀ C ^ M).support, MvPolynomial.coeff A (cayDet n₀ C ^ M) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ M)) = (∑ A ∈ (cayDet n₀ C ^ M).support, MvPolynomial.coeff A (cayDet n₀ C ^ M) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q)) * (∑ A ∈ (cayDet n₀ C ^ Y).support, MvPolynomial.coeff A (cayDet n₀ C ^ Y) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ Y))) := by
  first | exact @GlobalTheory.DetPowPairing.pairing_pow_proportional | exact GlobalTheory.DetPowPairing.pairing_pow_proportional | (intros; apply GlobalTheory.DetPowPairing.pairing_pow_proportional <;> assumption)
