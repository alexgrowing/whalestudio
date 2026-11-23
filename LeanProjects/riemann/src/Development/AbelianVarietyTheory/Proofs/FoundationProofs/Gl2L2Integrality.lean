import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset Filter Topology MeasureTheory

namespace GlobalTheory.PsiTail

open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

lemma pow_le_exp (b : ℝ) (hb : 0 < b) (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ n ≤ (n.factorial / b ^ n) * Real.exp (b * x) := by
  have h := Real.pow_div_factorial_le_exp (b * x) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [h]

lemma one_le_log {Q : ℝ} (hQ : 3 ≤ Q) : 1 ≤ Real.log Q := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma error_terms (c₁ : ℝ) (hc₁ : 0 < c₁) : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ Q u : ℝ, 3 ≤ Q → 2 ≤ u →
    (u ≤ Real.exp (Real.log Q ^ 2) → Real.log (u * Q) ^ 2 / Q ≤ K * Q ^ (-c) / Real.log u ^ 2) ∧
    (Real.exp (Real.log Q ^ 2) ≤ u →
      Real.exp (-c₁ * Real.sqrt (Real.log u)) ≤ K * Q ^ (-c) / Real.log u ^ 2) := by
  set K₁ : ℝ := (Nat.factorial 8 : ℝ) / (1 / 2) ^ 8 with hK₁
  set K₂ : ℝ := (Nat.factorial 4 : ℝ) / (c₁ / 2) ^ 4 with hK₂
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 < K₂ := by rw [hK₂]; positivity
  refine ⟨4 * K₁ + K₂, min (1 / 2) (c₁ / 2), by positivity, lt_min (by norm_num) (by positivity), ?_⟩
  intro Q u hQ hu
  have hQ0 : 0 < Q := by linarith
  have hu0 : 0 < u := by linarith
  have hL := one_le_log hQ
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  set L := Real.log Q with hLdef
  set c := min (1 / 2 : ℝ) (c₁ / 2) with hc
  have hQc : Q ^ (-c) = Real.exp (-(c * L)) := by
    rw [Real.rpow_def_of_pos hQ0]; congr 1; ring
  have hE : 0 < Real.exp (-(c * L)) := Real.exp_pos _
  rw [hQc]
  constructor
  · intro h
    have h1 : Real.log u ≤ L ^ 2 := by
      rw [Real.log_le_iff_le_exp hu0]; exact h
    have h2 : Real.log (u * Q) = Real.log u + L := Real.log_mul hu0.ne' hQ0.ne'
    have h3 : Real.log (u * Q) ≤ 2 * L ^ 2 := by rw [h2]; nlinarith
    have h3' : 0 ≤ Real.log (u * Q) := by rw [h2]; linarith
    have h4 : Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ 4 * L ^ 8 := by
      calc Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ (2 * L ^ 2) ^ 2 * (L ^ 2) ^ 2 := by gcongr
        _ = 4 * L ^ 8 := by ring
    have h5 : L ^ 8 ≤ K₁ * Real.exp (1 / 2 * L) := pow_le_exp (1 / 2) (by norm_num) 8 L (by linarith)
    have h6 : Real.exp (1 / 2 * L) ≤ Real.exp (-(c * L)) * Q := by
      have : Q = Real.exp L := (Real.exp_log hQ0).symm
      conv_rhs => rw [this]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : c ≤ 1 / 2 := min_le_left _ _
      nlinarith
    rw [div_le_div_iff₀ hQ0 (by positivity)]
    have h7 : K₁ * Real.exp (1 / 2 * L) ≤ K₁ * (Real.exp (-(c * L)) * Q) := by gcongr
    have h8 : 0 ≤ K₂ * (Real.exp (-(c * L)) * Q) := by positivity
    calc Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ 4 * L ^ 8 := h4
      _ ≤ 4 * (K₁ * (Real.exp (-(c * L)) * Q)) + K₂ * (Real.exp (-(c * L)) * Q) := by
        have := h5.trans h7
        linarith
      _ = _ := by ring
  · intro h
    have h1 : L ^ 2 ≤ Real.log u := by
      rw [Real.le_log_iff_exp_le hu0]; exact h
    set s := Real.sqrt (Real.log u) with hs
    have hs2 : s ^ 2 = Real.log u := Real.sq_sqrt hlu.le
    have hLs : L ≤ s := Real.le_sqrt_of_sq_le h1
    have h5 : s ^ 4 ≤ K₂ * Real.exp (c₁ / 2 * s) := pow_le_exp (c₁ / 2) (by positivity) 4 s (by linarith)
    have h6 : Real.exp (-c₁ * s) * Real.exp (c₁ / 2 * s) ≤ Real.exp (-(c * L)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h7 : c ≤ c₁ / 2 := min_le_right _ _
      have h8 : c * L ≤ c₁ / 2 * s := by gcongr
      linarith
    rw [le_div_iff₀ (by positivity), ← hs2]
    calc Real.exp (-c₁ * s) * (s ^ 2) ^ 2 = Real.exp (-c₁ * s) * s ^ 4 := by ring
      _ ≤ Real.exp (-c₁ * s) * (K₂ * Real.exp (c₁ / 2 * s)) := by gcongr
      _ = K₂ * (Real.exp (-c₁ * s) * Real.exp (c₁ / 2 * s)) := by ring
      _ ≤ K₂ * Real.exp (-(c * L)) := by gcongr
      _ ≤ (4 * K₁ + K₂) * Real.exp (-(c * L)) := by gcongr; linarith

lemma hasDerivAt_prim (Q E u : ℝ) (hQ : 0 < Q) (hu : 1 < u) :
    HasDerivAt (fun t : ℝ => -(t ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (t * Q) ^ 2 + 320000 * Real.log (t * Q) + 128000000) + E / Real.log t))
      ((u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u) u := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos hu
  have h1 : HasDerivAt (fun t : ℝ => t ^ (-(1 : ℝ) / 400)) ((-(1 : ℝ) / 400) * (u ^ (-(1 : ℝ) / 400) / u)) u := by
    have := Real.hasDerivAt_rpow_const (x := u) (p := -(1 : ℝ) / 400) (Or.inl hu0.ne')
    rwa [Real.rpow_sub_one hu0.ne'] at this
  have h2 : HasDerivAt (fun t : ℝ => Real.log (t * Q)) (1 / u) u := by
    have := ((hasDerivAt_id' u).mul_const Q).log (by positivity)
    refine this.congr_deriv ?_
    field_simp
  have h3 : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu0.ne'
  have h4 := ((h1.fun_mul ((((h2.fun_pow 2).const_mul 400).fun_add (h2.const_mul 320000)).add_const 128000000)).fun_add
    ((hasDerivAt_const u E).fun_div h3 hlu.ne')).fun_neg
  refine h4.congr_deriv ?_
  have := hlu.ne'
  have := hu0.ne'
  generalize u ^ (-(1 : ℝ) / 400) = w
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

theorem psi_tail_bound : PartialSumIntegralBound := by
  intro C₁ c₁ hC₁ hc₁
  obtain ⟨K, c, hK, hc, herr⟩ := error_terms c₁ hc₁
  refine ⟨C₁ * (128320401 + 5 * K), c, by positivity, hc, ?_⟩
  intro Q a hQ h1 h2 Z U hZ hZU
  have hQ0 : 0 < Q := by linarith
  have hL := one_le_log hQ
  set E := K * Q ^ (-c) with hE
  have hE0 : 0 < E := by rw [hE]; positivity
  have hpt : ∀ u : ℝ, 2 ≤ u →
      ‖psum a u‖ / u ≤ C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    rw [div_le_iff₀ hu0]
    rcases le_total u (Real.exp (Real.log Q ^ 2)) with h | h
    · have e := (herr Q u hQ hu).1 h
      have e1 : u ^ (1 - (1 : ℝ) / 400) = u ^ (-(1 : ℝ) / 400) * u := by
        rw [← Real.rpow_add_one hu0.ne']; congr 1; ring
      calc ‖psum a u‖ ≤ _ := h1 u hu
        _ = C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + Real.log (u * Q) ^ 2 / Q) * u := by
          rw [e1]; ring
        _ ≤ _ := by gcongr
    · have e := (herr Q u hQ hu).2 h
      have e1 : 0 ≤ u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 := by positivity
      calc ‖psum a u‖ ≤ _ := h2 u h
        _ = C₁ * Real.exp (-c₁ * Real.sqrt (Real.log u)) * u := by ring
        _ ≤ _ := by gcongr; linarith
  set g : ℝ → ℝ := fun u =>
    C₁ * ((u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u) with hg
  have hpt2 : ∀ u ∈ Set.Icc Z U, ‖psum a u‖ / u ^ 2 ≤ g u := by
    intro u hu
    have hu2 : 2 ≤ u := hZ.trans hu.1
    have hu0 : 0 < u := by linarith
    calc ‖psum a u‖ / u ^ 2 = ‖psum a u‖ / u / u := by field_simp
      _ ≤ C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u := by
        gcongr; exact hpt u hu2
      _ = g u := by rw [hg]; ring
  have hgc : ContinuousOn g (Set.Icc Z U) := by
    intro u hu
    have hu2 : 2 ≤ u := hZ.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlu : Real.log u ^ 2 ≠ 0 := (pow_pos (Real.log_pos (by linarith)) 2).ne'
    have huQ : u * Q ≠ 0 := mul_ne_zero hu0 hQ0.ne'
    apply ContinuousAt.continuousWithinAt
    rw [hg]
    fun_prop (disch := first | assumption | exact Or.inl hu0)
  have hgi : IntervalIntegrable g volume Z U := hgc.intervalIntegrable_of_Icc hZU
  have hmeas : Measurable (fun u : ℝ => ‖psum a u‖ / u ^ 2) := by
    have : Measurable (fun u : ℝ => ‖psum a u‖) :=
      (measurable_from_top (f := fun N : ℕ => ‖∑ n ∈ Icc 1 N, a n‖)).comp Nat.measurable_floor
    exact this.div (measurable_id.pow_const 2)
  have hfi : IntervalIntegrable (fun u : ℝ => ‖psum a u‖ / u ^ 2) volume Z U := by
    refine hgi.mono_fun' hmeas.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hZU]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt2 u (Set.Ioc_subset_Icc_self hu)
  have hint := intervalIntegral.integral_mono_on hZU hfi hgi hpt2
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := g)
    (f := fun t : ℝ => C₁ * -(t ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (t * Q) ^ 2 + 320000 * Real.log (t * Q) + 128000000) + E / Real.log t))
    (a := Z) (b := U) (fun u hu => by
      rw [Set.uIcc_of_le hZU] at hu
      exact (hasDerivAt_prim Q E u hQ0 (by linarith [hu.1])).const_mul C₁) hgi
  have hZ0 : 0 < Z := by linarith
  have hU0 : 0 < U := by linarith
  have hlU : 0 < Real.log U := Real.log_pos (by linarith)
  have hlUQ : 0 < Real.log (U * Q) := Real.log_pos (by nlinarith)
  have hlZ : 2 / 3 ≤ Real.log Z := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hZ
    linarith
  have hlZQ : 1 ≤ Real.log (Z * Q) := by rw [Real.log_mul hZ0.ne' hQ0.ne']; linarith
  have hUnn : 0 ≤ C₁ * (U ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (U * Q) ^ 2 + 320000 * Real.log (U * Q) + 128000000) + E / Real.log U) := by
    positivity
  have hZpt := hpt Z hZ
  set w := Z ^ (-(1 : ℝ) / 400) with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  set l := Real.log (Z * Q) with hl
  have b1 : 400 * l ^ 2 + 320000 * l + 128000000 ≤ 128320400 * l ^ 2 := by nlinarith
  have b2 : E / Real.log Z ≤ 2 * E := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have b3 : E / Real.log Z ^ 2 ≤ 3 * E := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ 3 * Real.log Z ^ 2 := by nlinarith
    nlinarith
  have hq : 0 < Q ^ (-c) := by positivity
  have hwl : 0 < w * l ^ 2 := by positivity
  calc ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2)
      ≤ C₁ * (w * l ^ 2 + E / Real.log Z ^ 2) +
        C₁ * (w * (400 * l ^ 2 + 320000 * l + 128000000) + E / Real.log Z) := by
        refine add_le_add hZpt (hint.trans ?_)
        rw [hval]
        linarith
    _ ≤ C₁ * (w * l ^ 2 + 3 * E) + C₁ * (w * (128320400 * l ^ 2) + 2 * E) := by gcongr
    _ = C₁ * (128320401 * (w * l ^ 2) + 5 * K * Q ^ (-c)) := by rw [hE]; ring
    _ ≤ C₁ * ((128320401 + 5 * K) * (w * l ^ 2 + Q ^ (-c))) := by
        gcongr
        nlinarith [mul_pos hK hwl]
    _ = _ := by ring

end GlobalTheory.PsiTail
