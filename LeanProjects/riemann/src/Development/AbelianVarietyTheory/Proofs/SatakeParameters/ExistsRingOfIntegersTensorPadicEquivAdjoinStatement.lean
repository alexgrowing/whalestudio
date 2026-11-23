import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingOfIntegersTensorPadicEquivAdjoin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime], ∃ κ : 𝓞 F ⊗[ℤ] ℤ_[ℓ] ≃+* cenOrder ℓ F, ∀ c : 𝓞 F, (κ (c ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := by
  first | (exact @GlobalTheory.CenOrderIso.cenOrder_equiv) | (exact GlobalTheory.CenOrderIso.cenOrder_equiv) | (intros; apply GlobalTheory.CenOrderIso.cenOrder_equiv  <;> assumption)
