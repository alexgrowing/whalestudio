import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrderPlacesAboveEqFinrankMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_order_placesAbove_eq_finrank_mul : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → (∀ s : Set (Place k F), s.Finite → (ρ ⁻¹' s).Finite) ∧ ∀ φ : Place k F → F, {v | ord v (φ v) ≠ 0}.Finite → ∑ᶠ p : Place k E, ord p (algebraMap F E (φ (ρ p))) = Module.finrank F E * ∑ᶠ v, ord v (φ v) := by
  first | exact @GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul | exact GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul | (intros; apply GlobalTheory.Nef.finsum_ord_pull_eq_finrank_mul <;> assumption)
