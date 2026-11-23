import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTorsionFreeOfCardQuotientPow
import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_eq_zero_of_pow_smul_of_card_quotient : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [AddCommGroup C] [Module ℤ_[l] C] [Module.Finite ℤ_[l] C], (∀ r : ℕ, 0 < r → Nat.card (C ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))) = l ^ r) → ∀ (r : ℕ) (c : C), (l : ℤ_[l]) ^ r • c = 0 → c = 0 := by
  first | exact @GlobalTheory.padicInt_torsionFree_of_card_quotient_pow | exact GlobalTheory.padicInt_torsionFree_of_card_quotient_pow | (intros; apply GlobalTheory.padicInt_torsionFree_of_card_quotient_pow <;> assumption)
