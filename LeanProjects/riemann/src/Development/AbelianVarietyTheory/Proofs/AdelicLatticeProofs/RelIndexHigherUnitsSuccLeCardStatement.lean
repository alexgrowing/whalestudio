import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexHigherUnitsSuccLeCard
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_higherUnits_succ_le_card : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) → (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧ (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by
  first | exact @GlobalTheory.QNorm.relIndex_hiUnits_succ_le | exact GlobalTheory.QNorm.relIndex_hiUnits_succ_le | (intros; apply GlobalTheory.QNorm.relIndex_hiUnits_succ_le <;> assumption)
