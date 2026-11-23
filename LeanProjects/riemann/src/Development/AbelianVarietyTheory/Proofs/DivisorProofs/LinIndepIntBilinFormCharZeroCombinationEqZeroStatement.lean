import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndepIntBilinFormCharZeroCombinationEqZero
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero : ∀ {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X) (k : Type) [Field k] [CharZero k] (a : Fin m → k), LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  first | exact @GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | exact GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero | (intros; apply GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero <;> assumption)
