import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem mulO {f g : V n → ℂ} {a b c : ℕ} (hf : f =O[𝓝 0] fun z => ‖z‖ ^ a)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ b) (h : a + b = c) :
    (fun z => f z * g z) =O[𝓝 0] fun z => ‖z‖ ^ c := by
  subst h
  exact (hf.mul hg).congr_right fun z => (pow_add _ _ _).symm

theorem pow_sub_pow {u v : V n → ℂ} (hu : u =O[𝓝 0] fun z => ‖z‖) (hv : v =O[𝓝 0] fun z => ‖z‖)
    (huv : (fun z => u z - v z) =O[𝓝 0] fun z => ‖z‖ ^ 2) (e : ℕ) :
    (fun z => u z ^ e - v z ^ e) =O[𝓝 0] fun z => ‖z‖ ^ (e + 1) := by
  rcases e with _ | e
  · simp only [pow_zero, sub_self]
    exact Asymptotics.isBigO_zero (fun z : V n => ‖z‖ ^ (0 + 1)) (𝓝 (0 : V n))
  · have hs : (fun z : V n => ∑ i ∈ Finset.range (e + 1), u z ^ i * v z ^ (e + 1 - 1 - i)) =O[𝓝 0]
        fun z : V n => ‖z‖ ^ e := by
      have hterm : ∀ i ∈ Finset.range (e + 1), (fun z : V n => u z ^ i * v z ^ (e + 1 - 1 - i)) =O[𝓝 0]
          fun z : V n => ‖z‖ ^ e := by
        intro i hi
        have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        refine ((hu.pow i).mul (hv.pow (e + 1 - 1 - i))).congr_right fun z => ?_
        rw [← pow_add]
        congr 1
        omega
      exact (Asymptotics.IsBigO.sum hterm).congr_left fun z => Finset.sum_apply z _ _
    refine ((hs.mul huv).congr_left fun z => ?_).congr_right fun z => ?_
    · exact (Commute.all (u z) (v z)).geom_sum₂_mul (e + 1)
    · ring

theorem prod_pow_O {ι : Type*} (s : Finset ι) (u : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) :
    (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
    exact Asymptotics.isBigO_const_const (1 : ℂ) one_ne_zero _
  · intro a s ha ih
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mulO ((hu a).pow (e a)) ih rfl

theorem prod_pow_sub {ι : Type*} (s : Finset ι) (u v : ι → V n → ℂ) (e : ι → ℕ)
    (hu : ∀ i, u i =O[𝓝 0] fun z => ‖z‖) (hv : ∀ i, v i =O[𝓝 0] fun z => ‖z‖)
    (huv : ∀ i, (fun z => u i z - v i z) =O[𝓝 0] fun z => ‖z‖ ^ 2) :
    (fun z => ∏ i ∈ s, u i z ^ e i - ∏ i ∈ s, v i z ^ e i) =O[𝓝 0]
      fun z => ‖z‖ ^ (∑ i ∈ s, e i + 1) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, sub_self]
    exact Asymptotics.isBigO_zero (fun z : V n => ‖z‖ ^ (∑ i ∈ (∅ : Finset ι), e i + 1)) (𝓝 (0 : V n))
  · intro a s ha ih
    have hc : e a + (∑ i ∈ s, e i + 1) = ∑ i ∈ insert a s, e i + 1 := by
      have := Finset.sum_insert ha (f := e); omega
    have hc' : (e a + 1) + ∑ i ∈ s, e i = ∑ i ∈ insert a s, e i + 1 := by
      have := Finset.sum_insert ha (f := e); omega
    have h1 := mulO ((hu a).pow (e a)) ih hc
    have h2 := mulO (pow_sub_pow (hu a) (hv a) (huv a) (e a)) (prod_pow_O s v e hv) hc'
    refine (h1.add h2).congr_left fun z => ?_
    simp only [Finset.prod_insert ha]
    ring

theorem taylor2 {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g z - g 0 - fderiv ℂ g 0 z) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
  obtain ⟨p, hp⟩ := hg
  have h := hp.isBigO_sub_partialSum_pow 2
  rw [hp.hasFDerivAt.fderiv]
  refine h.congr_left fun z => ?_
  have e1 : (p 1 fun _ => z) = p 1 ![z] := by
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hp.coeff_zero, e1]
  try ring

theorem lower_of_deriv {φ : V n → V n} (L : V n ≃L[ℂ] V n)
    (h : (fun z => φ z - L z) =o[𝓝 0] fun z => z) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 0, c * ‖z‖ ≤ ‖φ z‖ := by
  set K : ℝ := ‖(L.symm : V n →L[ℂ] V n)‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  filter_upwards [h.def (show (0 : ℝ) < 1 / (2 * K) by positivity)] with z hz
  have h1 : ‖z‖ ≤ K * ‖L z‖ := by
    calc ‖z‖ = ‖(L.symm : V n →L[ℂ] V n) (L z)‖ := by simp
      _ ≤ ‖(L.symm : V n →L[ℂ] V n)‖ * ‖L z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖L z‖ := by gcongr; linarith
  have h2 : ‖L z‖ ≤ ‖φ z‖ + ‖φ z - L z‖ := by
    calc ‖L z‖ = ‖φ z - (φ z - L z)‖ := by congr 1; abel
      _ ≤ ‖φ z‖ + ‖φ z - L z‖ := norm_sub_le _ _
  have h3 : ‖z‖ / K ≤ ‖L z‖ := by rw [div_le_iff₀ hKpos]; linarith
  have h4 : ‖z‖ / K = 2 * (1 / (2 * K) * ‖z‖) := by field_simp; try ring
  linarith

theorem vanS_int (hn : 1 ≤ n) {a : ℕ} {G : V n → ℂ} {S : Fin n → V n → ℂ}
    (hG : G =O[𝓝 0] fun z => ‖z‖ ^ a) {c : ℝ} (hc : 0 < c)
    (hS : ∀ᶠ z in 𝓝 0, c * ‖z‖ ^ 2 ≤ ∑ k, ‖S k z‖ ^ 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖G z‖ ^ 2 *
      (∑ k, ‖S k z‖ ^ 2) ^ (-((a : ℝ) + (n : ℝ) - 1 / 2))) < ⊤ := by
  obtain ⟨C, hCpos, hC⟩ := hG.exists_pos
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hC.bound.and hS)
  refine ⟨ρ, hρ, ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set β : ℝ := (a : ℝ) + (n : ℝ) - 1 / 2 with hβ
  have hβpos : 0 < β := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  set K : ℝ := C ^ 2 * c ^ (-β) with hK
  have hKpos : 0 < K := by positivity
  have hfin : Module.finrank ℝ (V n) = 2 * n := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hgi : MeasureTheory.IntegrableOn (fun z : V n => K * ‖z‖ ^ (-(2 * (n : ℝ) - 1)))
      (Metric.ball 0 ρ) := by
    refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := K) (α := 2 * (n : ℝ) - 1) ?_ ?_ ?_ ?_
    · rw [hfin]; omega
    · rw [hfin]; push_cast; linarith
    · refine MeasureTheory.ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  have hlt := (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (MeasureTheory.ae_of_all _ fun z => by positivity)).mp hgi.2
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae ?_) hlt
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball,
    MeasureTheory.ae_restrict_of_ae (MeasureTheory.compl_mem_ae_iff.mpr
      (MeasureTheory.measure_singleton (0 : V n)))] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0'
  obtain ⟨h1, h2⟩ := hball z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
  apply ENNReal.ofReal_le_ofReal
  have e1 : ‖G z‖ ^ 2 ≤ C ^ 2 * ‖z‖ ^ (2 * a) := by
    calc ‖G z‖ ^ 2 ≤ (C * ‖z‖ ^ a) ^ 2 := by gcongr
      _ = C ^ 2 * ‖z‖ ^ (2 * a) := by ring
  have e2 : (∑ k, ‖S k z‖ ^ 2) ^ (-β) ≤ (c * ‖z‖ ^ 2) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have e3 : (c * ‖z‖ ^ 2) ^ (-β) = c ^ (-β) * ‖z‖ ^ (-2 * β) := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
    ring_nf
  have e4 : ‖z‖ ^ (2 * a) * ‖z‖ ^ (-2 * β) = ‖z‖ ^ (-(2 * (n : ℝ) - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hzpos]
    congr 1
    rw [hβ]
    push_cast
    ring
  calc ‖G z‖ ^ 2 * (∑ k, ‖S k z‖ ^ 2) ^ (-β) ≤ (C ^ 2 * ‖z‖ ^ (2 * a)) * (c * ‖z‖ ^ 2) ^ (-β) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = K * ‖z‖ ^ (-(2 * (n : ℝ) - 1)) := by rw [e3, hK, ← e4]; ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
