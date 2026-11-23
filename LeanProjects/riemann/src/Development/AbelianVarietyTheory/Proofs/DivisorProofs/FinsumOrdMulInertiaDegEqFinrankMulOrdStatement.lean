import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdMulInertiaDegEqFinrankMulOrd
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord' : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ringKrullDim A = 1 → ∀ a : A, a ≠ 0 → ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A}, ((Ring.ord (Localization.AtPrime Q.asIdeal) (algebraMap B _ (algebraMap A B a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg A : ℤ) = (Module.finrank A B : ℤ) * ((Ring.ord A a).toNat : ℤ) := by
  first | exact @GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | exact GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord | (intros; apply GlobalTheory.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord <;> assumption)
