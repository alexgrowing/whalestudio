import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFromPadicUniqueOfSepStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eq_zero_of_infinitely_p_divisible (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (x : O)
    (hx : ∀ n : ℕ, ∃ y : O, x = (p : O) ^ n * y) : x = 0 := by
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : O)})) x
  intro n
  obtain ⟨y, hy⟩ := hx n
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, hy]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem padic_ringHom_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], (∀ f : ℤ_[p] →+* O, f = padicToO p O) ∧ ∀ (h : ℕ) (f : ℤ_[p] →+* Matrix (Fin h) (Fin h) O) (c : ℤ_[p]), f c = padicToO p O c • (1 : Matrix (Fin h) (Fin h) O) := by
  intro p _ O _ _ _
  refine ⟨fun f => GlobalTheory.T.ring_hom_from_padic_unique_of_sep p O (eq_zero_of_infinitely_p_divisible p O) f _, fun h f c => ?_⟩
  have hsep : ∀ x : Matrix (Fin h) (Fin h) O,
      (∀ n : ℕ, ∃ y : Matrix (Fin h) (Fin h) O, x = ((p : ℕ) : Matrix (Fin h) (Fin h) O) ^ n * y) → x = 0 := by
    intro x hx
    ext i j
    apply eq_zero_of_infinitely_p_divisible p O
    intro n
    obtain ⟨y, hy⟩ := hx n
    refine ⟨y i j, ?_⟩
    rw [hy, ← Nat.cast_pow, ← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul, Nat.cast_pow]
  have := GlobalTheory.T.ring_hom_from_padic_unique_of_sep p (Matrix (Fin h) (Fin h) O) hsep f
    ((algebraMap O (Matrix (Fin h) (Fin h) O)).comp (padicToO p O))
  rw [this, RingHom.comp_apply, Algebra.algebraMap_eq_smul_one]

end GlobalTheory
