import Formalism.LocalToGlobal.Columns.TwQSplit
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section Cmp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* v.adicCompletion F)
  (hint : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) ≤ 1)
  (hPv : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal)

include hint hPv in
theorem qsp_val_one (t : 𝓞 E) (ht : t ∉ P.asIdeal) : Valued.v (φ (algebraMap (𝓞 E) E t)) = 1 :=
  le_antisymm (hint t) (not_lt.1 fun h => ht ((hPv t).1 h))

theorem qsp_frac (x : E) (hx : P.valuation E x ≤ 1) :
    ∃ (a : 𝓞 E) (t : 𝓞 E), t ∉ P.asIdeal ∧ x * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E a := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hnd
  have hd0 : (d : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hspan : Ideal.span {(d : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hd0
  have hPu : ¬ IsUnit P.asIdeal := by
    rw [Ideal.isUnit_iff]
    exact P.isPrime.ne_top
  obtain ⟨e, J, hPJ, hJ⟩ := WfDvdMonoid.max_power_factor' hspan hPu
  have hJP : ¬ J ≤ P.asIdeal := fun h => hPJ (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.1 hJP
  have hvd : P.intValuation (d : 𝓞 E) ≤ WithZero.exp (-(e : ℤ)) := by
    rw [P.intValuation_le_pow_iff_dvd, hJ]
    exact dvd_mul_right _ _
  have hvn : P.intValuation n ≤ WithZero.exp (-(e : ℤ)) := by
    refine le_trans ?_ hvd
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E n) ≤ P.valuation E (algebraMap (𝓞 E) E (d : 𝓞 E))
    rw [← hnd, map_mul]
    exact mul_le_of_le_one_left' hx
  have hnt : n * t ∈ Ideal.span {(d : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ((P.intValuation_le_pow_iff_mem n e).1 hvn) htJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hnt
  refine ⟨a, t, htP, ?_⟩
  have hD : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 hd0
  have hat : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E d =
      algebraMap (𝓞 E) E n * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, ha]
  apply mul_right_cancel₀ hD
  linear_combination (algebraMap (𝓞 E) E t) * hnd - hat

include hint hPv in

theorem qsp_le_of_val (x : E) (hx : P.valuation E x ≤ 1) : Valued.v (φ x) ≤ 1 := by
  obtain ⟨a, t, ht, hxt⟩ := qsp_frac P x hx
  have h1 := qsp_val_one P φ hint hPv t ht
  have h2 := hint a
  rw [← hxt, map_mul, Valuation.map_mul, h1, mul_one] at h2
  exact h2

include hint hPv in

theorem qsp_lt_of_val (x : E) (hx : P.valuation E x < 1) : Valued.v (φ x) < 1 := by
  obtain ⟨a, t, ht, hxt⟩ := qsp_frac P x hx.le
  have h1 := qsp_val_one P φ hint hPv t ht
  have ha : a ∈ P.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E a) < 1
    rw [← hxt, map_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 ht, mul_one]
    exact hx
  have h2 := (hPv a).2 ha
  rw [← hxt, map_mul, Valuation.map_mul, h1, mul_one] at h2
  exact h2

include hint hPv in

theorem qsp_val_iff (x : E) : Valued.v (φ x) ≤ 1 ↔ P.valuation E x ≤ 1 := by
  refine ⟨fun h => ?_, qsp_le_of_val P φ hint hPv x⟩
  by_contra hc
  rw [not_le] at hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hc
  have hinv : P.valuation E x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx0).1 hc
  have hlt := qsp_lt_of_val P φ hint hPv x⁻¹ hinv
  rw [map_inv₀] at hlt
  have hφ : φ x ≠ 0 := (map_ne_zero φ).2 hx0
  exact absurd h (not_le.2 ((Valuation.one_lt_val_iff _ hφ).2 hlt))

include hint hPv in

theorem qsp_mod (x d : E) (hd : d ≠ 0) (z : v.adicCompletion F) (hz : Valued.v z ≤ 1) (hxz : φ x = φ d * z) :
    P.valuation E x ≤ P.valuation E d := by
  have hφd : φ d ≠ 0 := (map_ne_zero φ).2 hd
  have h1 : φ (x / d) = z := by
    rw [map_div₀, hxz, mul_div_cancel_left₀ _ hφd]
  have h2 : P.valuation E (x / d) ≤ 1 := (qsp_val_iff P φ hint hPv _).1 (by rw [h1]; exact hz)
  have h3 : x = x / d * d := by rw [div_mul_cancel₀ _ hd]
  rw [h3, map_mul]
  exact mul_le_of_le_one_left' h2

end Cmp

end Formalism.L2.Col
