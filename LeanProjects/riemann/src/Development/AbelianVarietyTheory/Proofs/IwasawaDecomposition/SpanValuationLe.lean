import Mathlib

namespace GlobalTheory.SpanValuationBound

open IsDedekindDomain

theorem span_valuation_le {L : Type} [Field L] [NumberField L] {S : Set L}
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}
    (hS : ∀ x ∈ S, (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) :
    ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S,
      (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => simp
  | add y z _ _ hy hz =>
    exact le_trans (Valuation.map_add _ y z) (max_le hy hz)
  | smul a y _ hy =>
    rw [Algebra.smul_def, map_mul]
    calc (HeightOneSpectrum.valuation L w) (algebraMap _ L a) * (HeightOneSpectrum.valuation L w) y
        ≤ 1 * γ := mul_le_mul' (HeightOneSpectrum.valuation_le_one w a) hy
      _ = γ := one_mul γ

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {S : Set L} (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}, (∀ x ∈ S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) → ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ :=
  @fun _ _ _ _ w _ h => span_valuation_le w h

end GlobalTheory.SpanValuationBound
