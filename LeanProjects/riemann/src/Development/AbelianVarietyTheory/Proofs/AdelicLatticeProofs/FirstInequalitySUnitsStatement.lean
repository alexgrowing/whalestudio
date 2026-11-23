import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnits
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧ 2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ 2 ^ (tFin F δ S + tReal F δ) := by
  first | exact @GlobalTheory.QNorm.first_inequality_sUnits | exact GlobalTheory.QNorm.first_inequality_sUnits | (intros; apply GlobalTheory.QNorm.first_inequality_sUnits <;> assumption)
