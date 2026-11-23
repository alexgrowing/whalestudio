import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorEqTeichmullerOfFrobeniusEqPowSelf
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_eq_teichmuller_of_frobenius_eq_pow_self : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] [PerfectRing O l] (y : WittVector l O), WittVector.frobenius y = y ^ l → y = WittVector.teichmuller l (y.coeff 0) := by
  first | exact @GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow | exact GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow | (intros; apply GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow <;> assumption)
