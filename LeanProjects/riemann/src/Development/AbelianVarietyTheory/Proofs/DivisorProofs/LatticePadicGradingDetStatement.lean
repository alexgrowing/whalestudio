import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePadicGradingDet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_padic_grading_det : ∀ (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime] (j : K →+* ℂ_[p]) (L : Submodule (𝓞 K) (Fin g → K)) (x : Fin g → Fin g → K) (s : ℕ), (∀ i, x i ∈ L) → LinearIndependent K x → ¬ p ∣ s → (∀ v ∈ L, (s : K) • v ∈ Submodule.span (𝓞 K) (Set.range x)) → ∑ k : Fin g, lnGrP p j L k = - Real.log ‖j (Matrix.of fun i k => x k i).det‖ := by
  first | exact @GlobalTheory.LieRead.CovolBasis.sum_lnGrP_eq_neg_log_norm_det | exact GlobalTheory.LieRead.CovolBasis.sum_lnGrP_eq_neg_log_norm_det | (intros; apply GlobalTheory.LieRead.CovolBasis.sum_lnGrP_eq_neg_log_norm_det <;> assumption)
