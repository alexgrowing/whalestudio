import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.LogVandermondeProofs.GammaIntegralPolynomialBound

namespace Formalism.HermitianLattices.TraceIntegrality

open MeasureTheory Set Metric

open scoped Function ENNReal in
theorem separated_set_packing_bound : SeparatedSetPackingBound := by
  intro E _ _ _ s r δ hδ hr hs h
  borelize E
  let μ : Measure E := Measure.addHaar
  have δpos : 0 < δ / 2 := by positivity
  have ρpos : 0 < r + δ / 2 := by positivity
  set A := ⋃ c ∈ s, ball (c : E) (δ / 2) with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) (δ / 2)) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := h c hc d hd hcd
    linarith
  have A_subset : A ⊆ ball (0 : E) (r + δ / 2) := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    have := hs x hx
    linarith
  have I :
    (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ δpos]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) (r + δ / 2)) := measure_mono A_subset
      _ = ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (δ / 2) ^ Module.finrank ℝ E ≤ (r + δ / 2) ^ Module.finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg δpos.le _)] at this
  have e : 1 + 2 * r / δ = (r + δ / 2) / (δ / 2) := by
    field_simp
    ring
  rw [e, div_pow, le_div_iff₀ (pow_pos δpos _)]
  exact K

theorem layer_cake_bound : LayerCakeSumBound := by
  intro Y h g v hv hh hc
  obtain ⟨hint, hle⟩ := Formalism.LogVandermondeBounds.flipTwoThree.gamma_integral_polynomial_bound v g hv
  have hpi := Real.pi_pos
  set w : ℝ → ℝ := fun u => Real.pi * Real.exp (-Real.pi * u) with hw
  have hwpos : ∀ u, 0 ≤ w u := fun u => by positivity
  have hwint : IntegrableOn w (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -Real.pi) (by linarith) 0).const_mul _
  have key : ∀ F : Finset Y,
      ∑ y ∈ F, Real.exp (-Real.pi * h y) ≤ 2 ^ g * (1 + 4 * g * v / Real.pi) ^ g := by
    intro F
    have h1 : ∀ y, Real.exp (-Real.pi * h y) = ∫ u in Ioi 0, (Ioi (h y)).indicator w u := by
      intro y
      rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right (hh y)]
      simp only [hw]
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
      field_simp
    have hi : ∀ y, IntegrableOn ((Ioi (h y)).indicator w) (Ioi 0) := fun y =>
      hwint.indicator measurableSet_Ioi
    have hpt : ∀ u ∈ Ioi (0 : ℝ), ∑ y ∈ F, (Ioi (h y)).indicator w u ≤
        2 ^ g * (Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g) := by
      intro u hu
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
      obtain ⟨hfin, hcard⟩ := hc u hu0
      have e1 : ∑ y ∈ F, (Ioi (h y)).indicator w u = ((F.filter (fun y => h y < u)).card : ℝ) * w u := by
        simp only [Set.indicator_apply, mem_Ioi]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have e2 : (F.filter (fun y => h y < u)).card ≤ {y | h y ≤ u}.ncard := by
        rw [← Set.ncard_coe_finset]
        apply Set.ncard_le_ncard _ hfin
        intro y hy
        simp only [Finset.coe_filter, mem_ofPred_eq] at hy
        exact le_of_lt hy.2
      have e3 : ((F.filter (fun y => h y < u)).card : ℝ) ≤ 2 ^ g * (1 + 4 * u * v) ^ g :=
        le_trans (by exact_mod_cast e2) hcard
      rw [e1]
      calc ((F.filter (fun y => h y < u)).card : ℝ) * w u
          ≤ (2 ^ g * (1 + 4 * u * v) ^ g) * w u := mul_le_mul_of_nonneg_right e3 (hwpos u)
        _ = _ := by simp only [hw]; ring
    calc ∑ y ∈ F, Real.exp (-Real.pi * h y)
        = ∑ y ∈ F, ∫ u in Ioi 0, (Ioi (h y)).indicator w u := Finset.sum_congr rfl fun y _ => h1 y
      _ = ∫ u in Ioi 0, ∑ y ∈ F, (Ioi (h y)).indicator w u :=
          (integral_finsetSum F fun y _ => hi y).symm
      _ ≤ ∫ u in Ioi (0 : ℝ), 2 ^ g * (Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g) :=
          setIntegral_mono_on (integrable_finsetSum F fun y _ => hi y) (hint.const_mul _)
            measurableSet_Ioi hpt
      _ = 2 ^ g * ∫ u in Ioi (0 : ℝ), Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g :=
          integral_const_mul _ _
      _ ≤ 2 ^ g * (1 + 4 * g * v / Real.pi) ^ g := mul_le_mul_of_nonneg_left hle (by positivity)
  have hnn : (0 : Y → ℝ) ≤ fun y => Real.exp (-Real.pi * h y) := fun y => (Real.exp_pos _).le
  have hsum := Real.tsum_le_of_sum_le hnn key
  refine ⟨summable_of_sum_le hnn key, hsum, ?_⟩
  have hb : 1 + 4 * (g : ℝ) * v / Real.pi ≤ 2 + 8 * g * v := by
    have h3 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hgv : 0 ≤ 4 * (g : ℝ) * v := by positivity
    have : 4 * (g : ℝ) * v / Real.pi ≤ 4 * (g : ℝ) * v := div_le_self hgv h3
    linarith
  have hb0 : 0 ≤ 1 + 4 * (g : ℝ) * v / Real.pi := by positivity
  calc (2 : ℝ) ^ g * ∑' y, Real.exp (-Real.pi * h y)
      ≤ 2 ^ g * (2 ^ g * (1 + 4 * g * v / Real.pi) ^ g) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 ^ g * (1 + 4 * g * v / Real.pi) ^ g := by
        rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ 4 ^ g * (2 + 8 * g * v) ^ g :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb g) (by positivity)

end Formalism.HermitianLattices.TraceIntegrality
