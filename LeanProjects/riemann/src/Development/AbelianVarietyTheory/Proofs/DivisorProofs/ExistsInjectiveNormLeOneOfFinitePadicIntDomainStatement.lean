import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveNormLeOneOfFinitePadicIntDomain
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 → ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by
  first | exact @GlobalTheory.PadicEmb.exists_embedding | exact GlobalTheory.PadicEmb.exists_embedding | (intros; apply GlobalTheory.PadicEmb.exists_embedding <;> assumption)
