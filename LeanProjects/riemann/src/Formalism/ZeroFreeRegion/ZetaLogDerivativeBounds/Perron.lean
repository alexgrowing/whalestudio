import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.ZetaNonvanishing.MellinSgen

open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

lemma perron_Sz_eq_Sa : Formalism.Sz = Formalism.Sa (fun n => (Λ n : ℝ)) := rfl

lemma perron_Sz_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : Formalism.Sz x = 0 := by
  unfold Formalism.Sz
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hx0 : 0 ≤ x := by
    by_contra h
    push_neg at h
    have h1 := Nat.floor_of_nonpos h.le
    omega
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 hn.2
  have hn1 : n = 1 := by
    have h1 : (n : ℝ) ≤ 1 := hnx.trans hx
    have h2 : n ≤ 1 := by exact_mod_cast h1
    omega
  subst hn1
  simp [ArithmeticFunction.vonMangoldt_apply_one]

lemma perron_Sz_eq_sum_range {N : ℕ} {x : ℝ} (hx : x < N) :
    Formalism.Sz x = ∑ n ∈ Finset.range N, Λ n * Formalism.mxS n x := by
  rw [perron_Sz_eq_Sa, Formalism.Sa_eq_tsum _ (by simp)]
  refine tsum_eq_sum (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  have hxn : x < n := lt_of_lt_of_le hx (by exact_mod_cast hn)
  refine Formalism.a_mxS_eq_zero _ (by simp) x n ?_
  rw [Finset.mem_Icc]
  rintro ⟨h1, h2⟩
  have hx1 : 1 ≤ x := Nat.floor_pos.mp (by omega)
  have : (n : ℝ) ≤ x := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  linarith

lemma perron_continuous_mxS (n : ℕ) : Continuous (Formalism.mxS n) := by
  show Continuous (fun x : ℝ => max (x / n - 1) 0)
  exact ((continuous_id.div_const _).sub continuous_const).max continuous_const

lemma perron_Sz_continuousAt (y : ℝ) : ContinuousAt (fun x => (Formalism.Sz x : ℂ)) y := by
  have key : ∀ N : ℕ, ∀ x : ℝ, x < N →
      Formalism.Sz x = ∑ n ∈ Finset.range N, Λ n * max (x / n - 1) 0 := by
    intro N x hx
    unfold Formalism.Sz
    by_cases hx0 : 0 ≤ x
    · have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.range N := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_range]
        have h1 := (Nat.le_floor_iff hx0).1 hn.2
        exact_mod_cast lt_of_le_of_lt h1 hx
      calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
          = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * max (x / n - 1) 0 := by
            refine Finset.sum_congr rfl fun n hn => ?_
            rw [Finset.mem_Icc] at hn
            have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn.1
            have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 hn.2
            rw [max_eq_left]
            rw [sub_nonneg, le_div_iff₀ (by linarith)]
            linarith
        _ = ∑ n ∈ Finset.range N, Λ n * max (x / n - 1) 0 := by
            refine Finset.sum_subset hsub fun n _ hn => ?_
            rw [Finset.mem_Icc, not_and_or] at hn
            rcases hn with h | h
            · have h0 : n = 0 := by omega
              subst h0
              simp
            · have hxn : x < n := by
                by_contra hc
                push_neg at hc
                exact h ((Nat.le_floor_iff hx0).2 hc)
              have hn0 : (0:ℝ) < n := hx0.trans_lt hxn
              rw [max_eq_right, mul_zero]
              rw [sub_nonpos, div_le_one hn0]
              exact hxn.le
    · push_neg at hx0
      rw [show ⌊x⌋₊ = 0 from Nat.floor_of_nonpos hx0.le]
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      symm
      refine Finset.sum_eq_zero fun n _ => ?_
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have hn0 : (0:ℝ) < n := by exact_mod_cast h
        rw [max_eq_right, mul_zero]
        rw [sub_nonpos, div_le_one hn0]
        have : (1:ℝ) ≤ n := by exact_mod_cast h
        linarith
  have hyN : y < ((⌊y⌋₊ + 2 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one y
    push_cast
    linarith
  have hg : Continuous (fun x : ℝ => ((∑ n ∈ Finset.range (⌊y⌋₊ + 2), Λ n * max (x / n - 1) 0 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_finset_sum _ fun n _ =>
      continuous_const.mul (((continuous_id.div_const _).sub continuous_const).max continuous_const))
  refine hg.continuousAt.congr ?_
  filter_upwards [Iio_mem_nhds hyN] with x hx
  rw [key _ x hx]

lemma perron_norm_LSeries_le {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖LSeries ↗Λ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
  have hs : LSeriesSummable ↗Λ (σ₀ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have heq : ∀ n, ‖LSeries.term ↗Λ w n‖ = ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
    intro n
    simp [LSeries.norm_term_eq, hw]
  unfold LSeries
  calc ‖∑' n, LSeries.term ↗Λ w n‖ ≤ ∑' n, ‖LSeries.term ↗Λ w n‖ :=
        norm_tsum_le_tsum_norm (hs.norm.congr fun n => (heq n).symm)
    _ = ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by simp_rw [heq]

lemma perron_denom_bound {σ₀ : ℝ} (hσ : 1 < σ₀) (t : ℝ) :
    min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2) ≤ ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖ := by
  set m := min ((σ₀ - 1) ^ 2) 1 with hm
  have hm0 : 0 ≤ m := le_min (sq_nonneg _) zero_le_one
  have hm1 : m ≤ 1 := min_le_right _ _
  have hm2 : m ≤ (σ₀ - 1) ^ 2 := min_le_left _ _
  have hn1 : ‖((σ₀ : ℂ) + t * I)‖ ^ 2 = σ₀ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hn2 : ‖((σ₀ : ℂ) + t * I - 1)‖ ^ 2 = (σ₀ - 1) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have a0 : 0 ≤ m * (1 + t ^ 2) := by positivity
  have a1 : m * (1 + t ^ 2) ≤ σ₀ ^ 2 + t ^ 2 := by nlinarith
  have a2 : m * (1 + t ^ 2) ≤ (σ₀ - 1) ^ 2 + t ^ 2 := by nlinarith
  have key : (m * (1 + t ^ 2)) ^ 2 ≤ (σ₀ ^ 2 + t ^ 2) * ((σ₀ - 1) ^ 2 + t ^ 2) := by
    rw [sq]
    exact mul_le_mul a1 a2 a0 (by positivity)
  have e : (‖((σ₀ : ℂ) + t * I)‖ * ‖((σ₀ : ℂ) + t * I - 1)‖) ^ 2 =
      (σ₀ ^ 2 + t ^ 2) * ((σ₀ - 1) ^ 2 + t ^ 2) := by
    rw [mul_pow, hn1, hn2]
  rw [norm_mul]
  exact (pow_le_pow_iff_left₀ a0 (by positivity) two_ne_zero).1 (key.trans e.symm.le)

lemma perron_Fy_eq_LSeries (y : ℝ) (w : ℂ) (hw : 1 < w.re) :
    Fy y w = LSeries ↗Λ w * (y : ℂ) ^ w / (w * (w - 1)) := by
  unfold Fy
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  ring

lemma perron_continuous_Fy {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Continuous (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by
  have hU : ∀ t : ℝ, 1 < ((σ₀ : ℂ) + t * I).re := fun t => by simpa using hσ
  have hzd : DifferentiableOn ℂ riemannZeta {s : ℂ | 1 < s.re} := fun s hs =>
    (differentiableAt_riemannZeta (fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hderiv : ContinuousOn (deriv riemannZeta) {s : ℂ | 1 < s.re} :=
    ((hzd.analyticOnNhd hopen).deriv).continuousOn
  have hline : Continuous (fun t : ℝ => (σ₀ : ℂ) + t * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  unfold Fy
  refine Continuous.div (Continuous.mul (Continuous.neg (Continuous.div ?_ ?_ ?_)) ?_) ?_ ?_
  · exact hderiv.comp_continuous hline hU
  · exact hzd.continuousOn.comp_continuous hline hU
  · intro t
    exact riemannZeta_ne_zero_of_one_lt_re (hU t)
  · exact hline.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  · exact hline.mul (hline.sub continuous_const)
  · intro t
    have h1 := hU t
    refine mul_ne_zero ?_ ?_
    · intro h
      rw [h] at h1
      norm_num at h1
    · intro h
      rw [sub_eq_zero] at h
      rw [h] at h1
      simp at h1

lemma perron_integrable_Fy {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Integrable (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by
  have hm : 0 < min ((σ₀ - 1) ^ 2) 1 := lt_min (by nlinarith) one_pos
  have hS : 0 ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := tsum_nonneg fun n => norm_nonneg _
  have hbound : ∀ t : ℝ, ‖Fy y ((σ₀ : ℂ) + t * I)‖ ≤
      ((∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖) * y ^ σ₀ / min ((σ₀ - 1) ^ 2) 1) * (1 + t ^ 2)⁻¹ := by
    intro t
    have hre : 1 < ((σ₀ : ℂ) + t * I).re := by simpa using hσ
    have hre' : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    rw [perron_Fy_eq_LSeries y _ hre, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre']
    have hL := perron_norm_LSeries_le hσ ((σ₀ : ℂ) + t * I) hre'
    have hD := perron_denom_bound hσ t
    have hDpos : 0 < min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2) := by positivity
    have hy' : 0 < y ^ σ₀ := Real.rpow_pos_of_pos hy σ₀
    calc ‖LSeries ↗Λ ((σ₀ : ℂ) + t * I)‖ * y ^ σ₀ / ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖
        ≤ (∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖) * y ^ σ₀ / (min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2)) :=
          div_le_div₀ (mul_nonneg hS hy'.le) (mul_le_mul_of_nonneg_right hL hy'.le) hDpos hD
      _ = _ := by field_simp
  exact Integrable.mono' ((integrable_inv_one_add_sq).const_mul _)
    (perron_continuous_Fy hy hσ).aestronglyMeasurable (Filter.Eventually.of_forall hbound)

lemma perron_mellinSgen_Λ :
    Measurable (Formalism.Sa (fun n => (Λ n : ℝ))) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Formalism.Sa (fun n => (Λ n : ℝ)) x| * x ^ (-σ - 1))
      (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Formalism.Sa (fun n => (Λ n : ℝ)) x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => ((Λ n : ℝ) : ℂ)) s / (s * (s - 1)) := Formalism.mellinSgen (fun n => (Λ n : ℝ)) 1 (fun n => by
    rw [one_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg])

lemma perron_mellin_Sz {w : ℂ} (hw : 1 < w.re) :
    mellin (fun x : ℝ => (Formalism.Sz x : ℂ)) (-w) =
      -(deriv riemannZeta w / riemannZeta w) / (w * (w - 1)) := by
  have h1 := perron_mellinSgen_Λ.2.2 w hw
  rw [← perron_Sz_eq_Sa] at h1
  rw [mellin]
  have hzero : ∀ t ∈ Ioi (0:ℝ) \ Ioi 1, (t : ℂ) ^ (-w - 1) • ((Formalism.Sz t : ℝ) : ℂ) = 0 := by
    intro t ht
    have : t ≤ 1 := not_lt.1 ht.2
    rw [perron_Sz_eq_zero_of_le_one this]
    simp
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi zero_le_one) hzero]
  simp_rw [smul_eq_mul, mul_comm ((_ : ℂ) ^ (-w - 1))]
  rw [h1, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  ring

lemma perron_mellinConvergent {σ₀ : ℝ} (hσ : 1 < σ₀) :
    MellinConvergent (fun x : ℝ => (Formalism.Sz x : ℂ)) ((-σ₀ : ℝ) : ℂ) := by
  unfold MellinConvergent
  have h2 := perron_mellinSgen_Λ.2.1 σ₀ hσ
  rw [← perron_Sz_eq_Sa] at h2
  have hmeas : Measurable Formalism.Sz := by
    rw [perron_Sz_eq_Sa]; exact perron_mellinSgen_Λ.1
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (((-σ₀ : ℝ) : ℂ) - 1) • ((Formalism.Sz t : ℝ) : ℂ)) (Ioi 1) := by
    refine Integrable.mono' h2 ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.pow_const _).smul
        (Complex.continuous_ofReal.measurable.comp hmeas)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), Complex.norm_real,
        Real.norm_eq_abs]
      simp [mul_comm]
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ hI1
  refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp [perron_Sz_eq_zero_of_le_one ht.2]

lemma perron_verticalIntegrable {σ₀ : ℝ} (hσ : 1 < σ₀) :
    VerticalIntegrable (mellin (fun x : ℝ => (Formalism.Sz x : ℂ))) (-σ₀) := by
  unfold VerticalIntegrable
  have hF := (perron_integrable_Fy one_pos hσ).comp_neg
  have heq : (fun y : ℝ => mellin (fun x : ℝ => (Formalism.Sz x : ℂ)) (((-σ₀ : ℝ) : ℂ) + y * I)) =
      fun y : ℝ => Fy 1 ((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I) := by
    funext y
    have hre : 1 < ((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I).re := by simpa using hσ
    rw [show ((-σ₀ : ℝ) : ℂ) + y * I = -((σ₀ : ℂ) + ((-y : ℝ) : ℂ) * I) by push_cast; ring,
      perron_mellin_Sz hre]
    unfold Fy
    simp [Complex.one_cpow]
  rw [heq]
  exact hF

theorem perron_formula : Perron := by
  intro y hy σ₀ hσ
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  refine ⟨perron_integrable_Fy hy0 hσ, ?_⟩
  have hinv := mellinInv_mellin_eq (-σ₀) (fun x : ℝ => (Formalism.Sz x : ℂ)) hy0 (perron_mellinConvergent hσ)
    (perron_verticalIntegrable hσ) (perron_Sz_continuousAt y)
  rw [← hinv, mellinInv, Complex.real_smul]
  push_cast
  congr 1
  have hneg := integral_neg_eq_self (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) volume
  rw [← hneg]
  congr 1
  funext t
  have hre : 1 < ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I).re := by simpa using hσ
  rw [show -(σ₀ : ℂ) + t * I = -((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) by push_cast; ring,
    perron_mellin_Sz hre, neg_neg]
  unfold Fy
  rw [smul_eq_mul]
  ring

end Formalism.ZF
