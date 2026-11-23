import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientMatrices

namespace GlobalTheory.CommonDenominatorExistence

theorem exists_common_denominator {E : Type} [Field E] [NumberField E] {r : ℕ}
    {L : GlobalTheory.SW.Lt E r} (hL : Submodule.FG L) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ v ∈ L, ∀ (a : Fin r), ∃ (c : NumberField.RingOfIntegers E),
        (↑c : E) = (↑d : E) * v a := by
  obtain ⟨s, rfl⟩ := hL
  choose z hz using fun p : (Fin r → E) × Fin r =>
    IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) (p.1 p.2)
  let d : NumberField.RingOfIntegers E := ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin r)), ((z p).2 : _)
  refine ⟨d, Finset.prod_ne_zero_iff.mpr fun p _ => nonZeroDivisors.ne_zero (z p).2.2, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem g hg =>
    intro a
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun p => ((z p).2 : NumberField.RingOfIntegers E))
      (show (g, a) ∈ s ×ˢ (Finset.univ : Finset (Fin r)) from
        Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩)
    refine ⟨e * (z (g, a)).1, ?_⟩
    have h := hz (g, a)
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
    rw [show d = ((z (g, a)).2 : NumberField.RingOfIntegers E) * e from he]
    push_cast
    linear_combination (-(e : E)) * h
  | zero =>
    intro a
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro a
    obtain ⟨c1, h1⟩ := hx a
    obtain ⟨c2, h2⟩ := hy a
    refine ⟨c1 + c2, ?_⟩
    rw [Pi.add_apply, mul_add, ← h1, ← h2]
    push_cast
    ring
  | smul t x _ hx =>
    intro a
    obtain ⟨c1, h1⟩ := hx a
    refine ⟨t * c1, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    push_cast
    linear_combination (t : E) * h1

end GlobalTheory.CommonDenominatorExistence
