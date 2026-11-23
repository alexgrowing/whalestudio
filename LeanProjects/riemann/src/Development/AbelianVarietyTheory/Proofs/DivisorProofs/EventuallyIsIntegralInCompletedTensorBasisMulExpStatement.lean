import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntegralInCompletedTensorBasis_mul_explicit : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C, IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  first | (exact @GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (exact GlobalTheory.OrbFinAf.isIntV_mul_eventually') | (intros; apply GlobalTheory.OrbFinAf.isIntV_mul_eventually' <;> assumption)
