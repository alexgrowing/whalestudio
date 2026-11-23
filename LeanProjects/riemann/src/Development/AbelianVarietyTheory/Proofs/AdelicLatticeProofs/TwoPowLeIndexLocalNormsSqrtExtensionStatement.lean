import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowLeIndexLocalNormsSqrtExtension
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension : ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧ 2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  first | exact @GlobalTheory.QNorm.two_pow_le_index_locNorm | exact GlobalTheory.QNorm.two_pow_le_index_locNorm | (intros; apply GlobalTheory.QNorm.two_pow_le_index_locNorm <;> assumption)
