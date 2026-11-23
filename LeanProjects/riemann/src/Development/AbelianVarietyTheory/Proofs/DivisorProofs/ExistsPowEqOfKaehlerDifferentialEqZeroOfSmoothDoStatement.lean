import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDifferentialEqZeroOfSmoothDo
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero_of_smooth_domain : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (S : Type) [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S] (f : S), KaehlerDifferential.D k S f = 0 → ∃ h : S, h ^ p = f := by
  first | exact @GlobalTheory.exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain | exact GlobalTheory.exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain | (intros; apply GlobalTheory.exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain <;> assumption)
