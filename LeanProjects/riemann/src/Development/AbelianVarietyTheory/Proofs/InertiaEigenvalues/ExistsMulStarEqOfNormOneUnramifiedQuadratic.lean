import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotalDegreeCMulXMulX
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.NormUnits

theorem norm_sub_le_max' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_eq_of_norm_sub_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖x - y‖ < ‖y‖) :
    ‖x‖ = ‖y‖ := by
  apply le_antisymm
  · calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ max ‖x - y‖ ‖y‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = ‖y‖ := max_eq_right h.le
  · by_contra hlt
    push_neg at hlt
    have : ‖y‖ ≤ max ‖x‖ ‖x - y‖ := by
      calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
        _ ≤ max ‖x‖ ‖x - y‖ := norm_sub_le_max' _ _
    rcases le_max_iff.1 this with h1 | h1 <;> linarith

theorem exists_far_unit (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] :
    ∃ ζ : E, ‖ζ‖ = 1 ∧ ∀ b : F, 1 ≤ ‖ζ - algebraMap F E b‖ := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨y, hy⟩ := hU.star_ne
  have hyF : ∀ b : F, algebraMap F E b ≠ y := fun b hb => hy (by rw [← hb, hU.star_fix])
  let g : F → ℝ := fun b => ‖y - algebraMap F E b‖
  have hg : Continuous g := continuous_norm.comp (continuous_const.sub (continuous_algebraMap F E))
  obtain ⟨b₀, -, hmin⟩ := (isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn
    ⟨0, by simp⟩ hg.continuousOn
  have hmin' : ∀ b : F, g b₀ ≤ g b := by
    intro b
    by_cases hb : ‖b‖ ≤ ‖y‖
    · exact hmin (mem_closedBall_zero_iff.2 hb)
    · push_neg at hb
      have h0 : g b₀ ≤ g 0 := hmin (by simp)
      refine h0.trans ?_
      simp only [g, map_zero, sub_zero]
      by_contra hlt
      push_neg at hlt
      have : ‖algebraMap F E b‖ ≤ max ‖y‖ ‖y - algebraMap F E b‖ := by
        calc ‖algebraMap F E b‖ = ‖y - (y - algebraMap F E b)‖ := by rw [sub_sub_cancel]
          _ ≤ _ := norm_sub_le_max' _ _
      rw [norm_algebraMap'] at this
      rcases le_max_iff.1 this with h | h <;> linarith
  have hz0 : y - algebraMap F E b₀ ≠ 0 := sub_ne_zero.2 (hyF b₀).symm
  obtain ⟨x, hx⟩ := hU.unram (y - algebraMap F E b₀)
  have hnx : ‖algebraMap F E x‖ = ‖y - algebraMap F E b₀‖ := by rw [norm_algebraMap', hx]
  have hxE : algebraMap F E x ≠ 0 := by
    intro h; rw [h, norm_zero] at hnx; exact hz0 (norm_eq_zero.1 hnx.symm)
  refine ⟨(y - algebraMap F E b₀) / algebraMap F E x, ?_, fun b => ?_⟩
  · rw [norm_div, hnx, div_self (norm_ne_zero_iff.2 hz0)]
  · have e : (y - algebraMap F E b₀) / algebraMap F E x - algebraMap F E b =
        (y - algebraMap F E (b₀ + x * b)) / algebraMap F E x := by
      rw [map_add, map_mul]; field_simp; ring
    rw [e, norm_div, hnx, le_div_iff₀ (norm_pos_iff.2 hz0), one_mul]
    exact hmin' (b₀ + x * b)

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits

theorem fixed_mem_range (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (ζ : E) (hζ : ∀ b : F, 1 ≤ ‖ζ - algebraMap F E b‖) :
    ∀ w : E, star w = w → ∃ a : F, algebraMap F E a = w := by
  have hζF : ∀ b : F, algebraMap F E b ≠ ζ := fun b h => by
    have := hζ b; rw [h, sub_self, norm_zero] at this; linarith
  have hli : LinearIndependent F ![(1 : E), ζ] := by
    rw [LinearIndependent.pair_iff]
    intro c d h
    by_cases hd : d = 0
    · subst hd
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at h
      exact ⟨(map_eq_zero _).1 h, rfl⟩
    · exfalso
      have hdE : algebraMap F E d ≠ 0 := (map_ne_zero _).2 hd
      apply hζF (-(c / d))
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
      rw [map_neg, map_div₀]
      field_simp
      linear_combination (-1 : E) * h
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hU.finrank_eq])
  have hB : ⇑B = ![(1 : E), ζ] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hspan : ∀ w : E, ∃ a b : F, algebraMap F E a + algebraMap F E b * ζ = w := by
    intro w
    refine ⟨B.repr w 0, B.repr w 1, ?_⟩
    have := B.sum_repr w
    rw [Fin.sum_univ_two, hB] at this
    simpa [Algebra.smul_def] using this
  have hsζ : star ζ ≠ ζ := by
    intro h
    obtain ⟨y, hy⟩ := hU.star_ne
    obtain ⟨a, b, rfl⟩ := hspan y
    apply hy
    rw [star_add, star_mul, hU.star_fix, hU.star_fix, h, mul_comm]
  intro w hw
  obtain ⟨a, b, rfl⟩ := hspan w
  rw [star_add, star_mul, hU.star_fix, hU.star_fix] at hw
  have h0 : algebraMap F E b * (star ζ - ζ) = 0 := by linear_combination hw
  rcases mul_eq_zero.1 h0 with hb | hb
  · exact ⟨a, by rw [hb, zero_mul, add_zero]⟩
  · exact absurd (sub_eq_zero.1 hb) hsζ

theorem exists_trace_one (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (ζ : E) (hζ1 : ‖ζ‖ = 1) (hζ : ∀ b : F, 1 ≤ ‖ζ - algebraMap F E b‖)
    (s t : F) (hs : algebraMap F E s = ζ + star ζ) (ht : algebraMap F E t = ζ * star ζ) :
    ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1 := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  have hns : ‖star ζ‖ = 1 := by rw [hU.norm_star, hζ1]
  have hdiff : ‖ζ - star ζ‖ = 1 := by
    refine le_antisymm ((norm_sub_le_max' _ _).trans (by rw [hns, hζ1, max_self])) (not_lt.1 fun hlt => ?_)
    have h2le : ‖(2 : F)‖ ≤ 1 := by
      rw [← one_add_one_eq_two]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp)
    have h2E : ‖(2 : E)‖ = ‖(2 : F)‖ := by rw [← map_ofNat (algebraMap F E) 2, norm_algebraMap']
    rcases h2le.lt_or_eq with h2n | h2n
    · have htn : ‖t‖ ≤ 1 := by rw [← norm_algebraMap' E t, ht, norm_mul, hζ1, hns, one_mul]
      obtain ⟨r, hr1, hr⟩ := exists_sqrt_mod F t htn h2n
      have hζr : ‖ζ - algebraMap F E r‖ ≤ 1 :=
        (norm_sub_le_max' _ _).trans (max_le hζ1.le (by rw [norm_algebraMap']; exact hr1))
      have e1 : (ζ - algebraMap F E r) ^ 2 = ζ * (ζ - star ζ) + algebraMap F E (t - r ^ 2) -
          2 * algebraMap F E r * (ζ - algebraMap F E r) := by
        rw [map_sub, map_pow, ht]; ring
      have hA : ‖ζ * (ζ - star ζ)‖ < 1 := by rw [norm_mul, hζ1, one_mul]; exact hlt
      have hB : ‖algebraMap F E (t - r ^ 2)‖ < 1 := by rw [norm_algebraMap', norm_sub_rev]; exact hr
      have hC : ‖2 * algebraMap F E r * (ζ - algebraMap F E r)‖ < 1 := by
        rw [norm_mul, norm_mul, h2E, norm_algebraMap']
        calc ‖(2 : F)‖ * ‖r‖ * ‖ζ - algebraMap F E r‖ ≤ ‖(2 : F)‖ * 1 * 1 := by gcongr
          _ < 1 := by simpa using h2n
      have hsq : ‖ζ - algebraMap F E r‖ ^ 2 < 1 := by
        rw [← norm_pow, e1]
        exact (norm_sub_le_max' _ _).trans_lt
          (max_lt ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hA hB)) hC)
      have := hζ r
      nlinarith [norm_nonneg (ζ - algebraMap F E r)]
    · have h2E1 : ‖(2 : E)‖ = 1 := h2E.trans h2n
      have h2ne : (2 : E) ≠ 0 := by intro h; rw [h, norm_zero] at h2E1; exact zero_ne_one h2E1
      have e1 : ζ - algebraMap F E (s / 2) = (ζ - star ζ) / 2 := by
        rw [map_div₀, hs, map_ofNat]; field_simp; ring
      have := hζ (s / 2)
      rw [e1, norm_div, h2E1, div_one] at this
      linarith
  have hne : ζ - star ζ ≠ 0 := by intro h; rw [h, norm_zero] at hdiff; exact zero_ne_one hdiff
  have hne' : star ζ - ζ ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 hne
  refine ⟨ζ / (ζ - star ζ), by rw [norm_div, hζ1, hdiff, div_one], ?_⟩
  rw [star_div₀, star_sub, star_star]
  field_simp
  ring

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits

theorem norm_onto_units : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (u : F), ‖u‖ = 1 → ∃ v : E, v * star v = algebraMap F E u := by
  intro F E _ _ _ _ hU u hu
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : CharZero F := hU.charZero
  have hN : ∀ v : E, ‖v * star v‖ = ‖v‖ ^ 2 := fun v => by rw [norm_mul, hU.norm_star, sq]
  have hsc : Continuous (fun y : E => star y) := by
    have : LipschitzWith 1 (fun y : E => star y) := LipschitzWith.of_dist_le_mul fun x y => by
      simp [dist_eq_norm, ← star_sub, hU.norm_star]
    exact this.continuous

  obtain ⟨ζ, hζ1, hζ⟩ := exists_far_unit F E
  have hfix := fixed_mem_range F E ζ hζ
  obtain ⟨s, hs⟩ := hfix (ζ + star ζ) (by rw [star_add, star_star, add_comm])
  obtain ⟨t, ht⟩ := hfix (ζ * star ζ) (by rw [star_mul, star_star, mul_comm])
  obtain ⟨e, he1, he⟩ := exists_trace_one F E ζ hζ1 hζ s t hs ht
  have hsn : ‖s‖ ≤ 1 := by
    rw [← norm_algebraMap' E s, hs]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hζ1.le (by rw [hU.norm_star, hζ1]))
  have htn : ‖t‖ = 1 := by
    rw [← norm_algebraMap' E t, ht, hN, hζ1, one_pow]
  obtain ⟨a, b, z, -, hb, hz, hone, hQ⟩ := exists_point_mod F _ _ u hsn htn.le hu.le
  have hw : (algebraMap F E a + algebraMap F E b * ζ) * star (algebraMap F E a + algebraMap F E b * ζ) =
      algebraMap F E (a ^ 2 + s * a * b + t * b ^ 2) := by
    have hsw : star (algebraMap F E a + algebraMap F E b * ζ) = algebraMap F E a + algebraMap F E b * star ζ := by
      rw [star_add, star_mul, hU.star_fix, hU.star_fix, mul_comm]
    rw [hsw]
    simp only [map_add, map_mul, map_pow, hs, ht]
    ring
  have hwb : ‖b‖ ≤ ‖algebraMap F E a + algebraMap F E b * ζ‖ := by
    by_cases hb0 : b = 0
    · simp [hb0]
    · have hbE : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb0
      have e1 : algebraMap F E a + algebraMap F E b * ζ = algebraMap F E b * (ζ - algebraMap F E (-(a / b))) := by
        rw [map_neg, map_div₀, sub_neg_eq_add]; field_simp; ring
      rw [e1, norm_mul, norm_algebraMap']
      exact le_mul_of_one_le_right (norm_nonneg _) (hζ _)
  have hz1 : ‖z‖ = 1 := by
    refine le_antisymm hz (not_lt.1 fun hzl => ?_)
    have hcz : ‖u * z ^ 2‖ < 1 := by
      rw [norm_mul, norm_pow, hu, one_mul]; exact pow_lt_one₀ (norm_nonneg _) hzl two_ne_zero
    have hQ1 : ‖a ^ 2 + s * a * b + t * b ^ 2‖ < 1 := by
      have := IsUltrametricDist.norm_add_le_max (a ^ 2 + s * a * b + t * b ^ 2 - u * z ^ 2) (u * z ^ 2)
      rw [sub_add_cancel] at this
      exact this.trans_lt (max_lt hQ hcz)
    have hw1 : ‖algebraMap F E a + algebraMap F E b * ζ‖ < 1 := by
      have : ‖algebraMap F E a + algebraMap F E b * ζ‖ ^ 2 < 1 := by
        rw [← hN, hw, norm_algebraMap']; exact hQ1
      nlinarith [norm_nonneg (algebraMap F E a + algebraMap F E b * ζ)]
    have hb1 : ‖b‖ < 1 := hwb.trans_lt hw1
    have ha1 : ‖a‖ < 1 := by
      rw [← norm_algebraMap' E a]
      have : algebraMap F E a = (algebraMap F E a + algebraMap F E b * ζ) - algebraMap F E b * ζ := by ring
      rw [this]
      refine (norm_sub_le_max' _ _).trans_lt (max_lt hw1 ?_)
      rw [norm_mul, norm_algebraMap', hζ1, mul_one]; exact hb1
    rcases hone with h | h | h <;> linarith
  have hzE : algebraMap F E z ≠ 0 := (map_ne_zero _).2 (by rintro rfl; simp at hz1)
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : E, ‖v₁ * star v₁ - algebraMap F E u‖ < 1 := by
    refine ⟨(algebraMap F E a + algebraMap F E b * ζ) / algebraMap F E z, ?_⟩
    have e1 : (algebraMap F E a + algebraMap F E b * ζ) / algebraMap F E z *
        star ((algebraMap F E a + algebraMap F E b * ζ) / algebraMap F E z) - algebraMap F E u =
        algebraMap F E ((a ^ 2 + s * a * b + t * b ^ 2 - u * z ^ 2) / z ^ 2) := by
      rw [star_div₀, hU.star_fix, div_mul_div_comm, hw]
      simp only [map_div₀, map_sub, map_mul, map_pow, map_add]
      field_simp
    rw [e1, norm_algebraMap', norm_div, norm_pow, hz1, one_pow, div_one]
    exact hQ

  let f : E → ℝ := fun v => ‖v * star v - algebraMap F E u‖
  have hf : Continuous f := continuous_norm.comp ((continuous_id.mul hsc).sub continuous_const)
  have hsph : ∀ v : E, f v < 1 → v ∈ Metric.sphere (0 : E) 1 := by
    intro v hv
    rw [mem_sphere_zero_iff_norm]
    have h1 : ‖v * star v‖ = 1 := by
      rw [norm_eq_of_norm_sub_lt (hv.trans_le (by rw [norm_algebraMap', hu])), norm_algebraMap', hu]
    rw [hN] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  obtain ⟨v₀, hv₀S, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn ⟨v₁, hsph v₁ hv₁⟩ hf.continuousOn
  have hv₀1 : ‖v₀‖ = 1 := mem_sphere_zero_iff_norm.1 hv₀S
  have hρ1 : f v₀ < 1 := (hmin (hsph v₁ hv₁)).trans_lt hv₁
  by_cases hρ0 : f v₀ = 0
  · exact ⟨v₀, sub_eq_zero.1 (norm_eq_zero.1 hρ0)⟩
  exfalso
  have hρpos : 0 < f v₀ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hρ0)
  have hN₀ : ‖v₀ * star v₀‖ = 1 := by rw [hN, hv₀1, one_pow]
  have hN₀0 : v₀ * star v₀ ≠ 0 := by intro h; rw [h, norm_zero] at hN₀; exact zero_ne_one hN₀
  obtain ⟨x, hxN, hxn, hsx⟩ : ∃ x : E, v₀ * star v₀ * (1 + x) = algebraMap F E u ∧ ‖x‖ = f v₀ ∧ star x = x := by
    refine ⟨algebraMap F E u / (v₀ * star v₀) - 1, ?_, ?_, ?_⟩
    · rw [show (1 : E) + (algebraMap F E u / (v₀ * star v₀) - 1) = algebraMap F E u / (v₀ * star v₀) by ring,
        mul_div_cancel₀ _ hN₀0]
    · have : algebraMap F E u / (v₀ * star v₀) - 1 = (algebraMap F E u - v₀ * star v₀) / (v₀ * star v₀) := by
        rw [sub_div, div_self hN₀0]
      rw [this, norm_div, hN₀, div_one, norm_sub_rev]
    · rw [star_sub, star_one, star_div₀, hU.star_fix, star_mul, star_star]
  have hyn : ‖x * e‖ ≤ f v₀ := by rw [norm_mul, hxn]; exact mul_le_of_le_one_right hρpos.le he1
  have hv'S : v₀ * (1 + x * e) ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_mul, hv₀1, one_mul,
      norm_eq_of_norm_sub_lt (by rw [add_sub_cancel_left, norm_one]; exact hyn.trans_lt hρ1), norm_one]
  have hfv' : f (v₀ * (1 + x * e)) = ‖x * e‖ ^ 2 := by
    have e1 : v₀ * (1 + x * e) * star (v₀ * (1 + x * e)) - algebraMap F E u =
        v₀ * star v₀ * (x * e * (x * star e)) := by
      rw [star_mul, star_add, star_one, star_mul, hsx]
      linear_combination (v₀ * star v₀ * x) * he + hxN
    show ‖v₀ * (1 + x * e) * star (v₀ * (1 + x * e)) - algebraMap F E u‖ = _
    rw [e1, norm_mul, hN₀, one_mul, norm_mul (x * e), norm_mul x (star e), hU.norm_star, norm_mul, sq]
  have hle : f v₀ ≤ f (v₀ * (1 + x * e)) := hmin hv'S
  rw [hfv'] at hle
  have : ‖x * e‖ ^ 2 ≤ f v₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyn 2
  nlinarith

end GlobalTheory.NormUnits
