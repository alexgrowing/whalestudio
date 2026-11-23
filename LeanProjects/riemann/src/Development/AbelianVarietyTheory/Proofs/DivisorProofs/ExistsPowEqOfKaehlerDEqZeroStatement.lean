import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZero
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (K : Type) [Field K] [Algebra k K] (f : K), KaehlerDifferential.D k K f = 0 → ∃ h : K, h ^ p = f := by
  first | exact @GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero | exact GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero | (intros; apply GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero <;> assumption)
