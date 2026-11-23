import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralNormSqLp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieveStatement

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.HybridLargeSieve

theorem sum_integral_le {ι : Type*} (s : Finset ι) (μ : Measure ℝ) (f : ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) (h0 : ∀ᵐ x ∂μ, ∀ i, 0 ≤ f i x)
    (hG : Integrable G μ) (h : ∀ᵐ x ∂μ, ∑ i ∈ s, f i x ≤ G x) :
    ∑ i ∈ s, ∫ x, f i x ∂μ ≤ ∫ x, G x ∂μ := by
  have hint : ∀ i ∈ s, Integrable (f i) μ := by
    intro i hi
    refine hG.mono' (hm i) ?_
    filter_upwards [h0, h] with x hx0 hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hx0 i)]
    exact (Finset.single_le_sum (fun j _ => hx0 j) hi).trans hx
  rw [← integral_finsetSum s hint]
  exact integral_mono_ae (integrable_finsetSum s hint) hG h

theorem kernel_eq (n δ x : ℝ) :
    (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) =
      (Set.Ico (n / Real.exp δ) n).indicator (fun x => 1 / x) x := by
  have he := Real.exp_pos δ
  by_cases hx : x < n ∧ n ≤ x * Real.exp δ
  · have hmem : x ∈ Set.Ico (n / Real.exp δ) n := ⟨(div_le_iff₀ he).2 hx.2, hx.1⟩
    rw [if_pos hx, Set.indicator_of_mem hmem]
  · have hmem : x ∉ Set.Ico (n / Real.exp δ) n := fun hm => hx ⟨hm.2, (div_le_iff₀ he).1 hm.1⟩
    rw [if_neg hx, Set.indicator_of_notMem hmem]

theorem kernel_integral (n δ : ℝ) (hn : 0 < n) (hδ : 0 ≤ δ) :
    IntegrableOn (fun x : ℝ => if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) = δ := by
  have he := Real.exp_pos δ
  have ha : 0 < n / Real.exp δ := div_pos hn he
  have hfun : (fun x : ℝ => if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) =
      (Set.Ico (n / Real.exp δ) n).indicator (fun x => 1 / x) := funext (kernel_eq n δ)
  have hcont : ContinuousOn (fun x : ℝ => 1 / x) (Set.Icc (n / Real.exp δ) n) :=
    continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
  have hI : IntegrableOn (fun x : ℝ => 1 / x) (Set.Ico (n / Real.exp δ) n) :=
    hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hsub : Set.Ico (n / Real.exp δ) n ⊆ Set.Ioi 0 := fun x hx => ha.trans_le hx.1
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ico).2 hI).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.2 hsub,
    integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (div_le_self hn.le (Real.one_le_exp hδ)),
    integral_one_div_of_pos ha hn, div_div_cancel₀ hn.ne', Real.log_exp]

theorem window (Q N : ℕ) (a : ℕ → ℂ) (T x : ℝ) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hx : 0 < x) :
    ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive},
      ‖∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤
    ∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
      ((Q : ℝ) ^ 2 + 8 * (2 * n / T + 1)) * ‖a n‖ ^ 2 := by
  set S := (Finset.Icc 1 N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)) with hS
  have hT0 : 0 < T := by linarith
  have hu0 : 0 ≤ 1 / T := by positivity
  have hu1 : 1 / T ≤ 1 := by rw [div_le_one hT0]; exact hT
  have hxy : x ≤ x * Real.exp (1 / T) := le_mul_of_one_le_right hx.le (Real.one_le_exp hu0)
  have hML : ⌊x⌋₊ + (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊) = ⌊x * Real.exp (1 / T)⌋₊ :=
    Nat.add_sub_cancel' (Nat.floor_mono hxy)
  have hsub : S ⊆ Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊)) := by
    intro n hn
    have hn' := (Finset.mem_filter.1 hn).2
    rw [Finset.mem_Ioc, hML]
    exact ⟨(Nat.floor_lt hx.le).2 hn'.1, Nat.le_floor hn'.2⟩
  have hL : ((⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ 2 * x / T + 1 := by
    rw [Nat.cast_sub (Nat.floor_mono hxy)]
    have h1 := Nat.floor_le (hx.le.trans hxy)
    have h2 := Nat.sub_one_lt_floor x
    have h3 : Real.exp (1 / T) - 1 ≤ 2 * (1 / T) := by
      have := Real.abs_exp_sub_one_le (x := 1 / T) (by rw [abs_of_nonneg hu0]; exact hu1)
      rw [abs_of_nonneg hu0] at this
      exact (le_abs_self _).trans this
    have h4 : x * (Real.exp (1 / T) - 1) ≤ x * (2 * (1 / T)) := mul_le_mul_of_nonneg_left h3 hx.le
    have h5 : x * (2 * (1 / T)) = 2 * x / T := by ring
    nlinarith
  let b : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have key := GlobalTheory.T.sum_norm_sq_primitive_char_sum_le Q ⌊x⌋₊ (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊) b hQ
  have hinner : ∀ (q : ℕ) (χ : DirichletCharacter ℂ (q + 1)),
      ∑ n ∈ S, a n * χ (n : ZMod (q + 1)) =
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊)), b n * χ (n : ZMod (q + 1)) := by
    intro q χ
    calc ∑ n ∈ S, a n * χ (n : ZMod (q + 1)) = ∑ n ∈ S, b n * χ (n : ZMod (q + 1)) :=
          Finset.sum_congr rfl (fun n hn => by simp [b, hn])
      _ = _ := Finset.sum_subset hsub (fun n _ hn => by simp [b, hn])
  have hR : ∑ n ∈ Finset.Ioc ⌊x⌋₊ (⌊x⌋₊ + (⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊)), ‖b n‖ ^ 2 =
      ∑ n ∈ S, ‖a n‖ ^ 2 := by
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [b, hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [b, hn])
  simp only [hinner]
  refine key.trans ?_
  rw [hR, Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hxn : x < n := (Finset.mem_filter.1 hn).2.1
  have h2 : 2 * x / T + 1 ≤ 2 * n / T + 1 := by gcongr
  have h3 : 0 ≤ 2 * (n : ℝ) / T + 1 := by positivity
  have h4 := Real.pi_le_four
  have h5 := Real.pi_pos
  have h6 : ((⌊x * Real.exp (1 / T)⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ 2 * n / T + 1 := hL.trans h2
  nlinarith

private theorem sum_finsum_primitive_eq_sum_sigma (Q : ℕ) (g : (q : ℕ) → DirichletCharacter ℂ (q + 1) → ℝ) :
    ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, g q χ =
      ∑ p ∈ (Finset.range Q).sigma
        (fun q => (Set.toFinite {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}).toFinset),
        g p.1 p.2 := by
  rw [Finset.sum_sigma]
  exact Finset.sum_congr rfl (fun q _ => finsum_mem_eq_finite_toFinset_sum _ _)

private theorem measurable_sum_filter_Icc_window (N : ℕ) (c : ℕ → ℂ) (δ : ℝ) :
    Measurable (fun x : ℝ => ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp δ), c n) := by
  have e : (fun x : ℝ => ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp δ), c n) =
      fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, if x < n ∧ (n : ℝ) ≤ x * Real.exp δ then c n else 0 := by
    funext x
    rw [Finset.sum_filter]
  rw [e]
  refine Finset.measurable_sum _ (fun n _ => Measurable.ite ?_ measurable_const measurable_const)
  exact (measurableSet_lt measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_id.mul measurable_const))

theorem hybrid_large_sieve : ∃ C : ℝ, 0 < C ∧ ∀ (Q N : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ Q → 1 ≤ T →
    ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive},
      (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod (q + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hGal⟩ := GlobalTheory.GallagherLemma.gallagher
  refine ⟨16 * C, by positivity, fun Q N a T hQ hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hδ0 : 0 ≤ 1 / T := by positivity
  let W : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) → ℝ → ℂ := fun p x =>
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
      a n * p.2 (n : ZMod (p.1 + 1))
  let c : ℕ → ℝ := fun n => ((Q : ℝ) ^ 2 + 8 * (2 * n / T + 1)) * ‖a n‖ ^ 2
  let K : ℕ → ℝ → ℝ := fun n x => if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0
  have hKint : ∀ n ∈ Finset.Icc 1 N,
      IntegrableOn (K n) (Set.Ioi 0) ∧ ∫ x in Set.Ioi (0 : ℝ), K n x = 1 / T := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    exact kernel_integral n (1 / T) hn0 hδ0
  have hGint : Integrable (fun x => ∑ n ∈ Finset.Icc 1 N, c n * K n x)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_finsetSum _ (fun n hn => (hKint n hn).1.const_mul (c n))
  have hstep1 : ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive},
      (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod (q + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∑ p ∈ (Finset.range Q).sigma
        (fun q => (Set.toFinite {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}).toFinset),
        ∫ x in Set.Ioi (0 : ℝ), ‖W p x‖ ^ 2 / x := by
    refine (sum_finsum_primitive_eq_sum_sigma Q _).trans_le ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ => hGal N (fun n => a n * p.2 (n : ZMod (p.1 + 1))) T hT)
  have hstep2 : ∑ p ∈ (Finset.range Q).sigma
        (fun q => (Set.toFinite {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}).toFinset),
        ∫ x in Set.Ioi (0 : ℝ), ‖W p x‖ ^ 2 / x ≤
      ∫ x in Set.Ioi (0 : ℝ), ∑ n ∈ Finset.Icc 1 N, c n * K n x := by
    refine sum_integral_le _ _ (fun p x => ‖W p x‖ ^ 2 / x) _
      (fun p => (((measurable_sum_filter_Icc_window N (fun n => a n * p.2 (n : ZMod (p.1 + 1))) (1 / T)).norm.pow_const
        2).div measurable_id).aestronglyMeasurable) ?_ hGint ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall (fun x hx p => div_nonneg (by positivity) (le_of_lt hx)))
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx0 : 0 < x := hx
      have e := sum_finsum_primitive_eq_sum_sigma Q (fun q (χ : DirichletCharacter ℂ (q + 1)) =>
        ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
          a n * χ (n : ZMod (q + 1))‖ ^ 2)
      have e2 : ∑ p ∈ (Finset.range Q).sigma
          (fun q => (Set.toFinite {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}).toFinset),
          ‖W p x‖ ^ 2 = _ := e.symm
      rw [← Finset.sum_div, e2]
      refine (div_le_div_of_nonneg_right (window Q N a T x hQ hT hx0) hx0.le).trans (le_of_eq ?_)
      rw [Finset.sum_div, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp only [c, K]
      split_ifs <;> ring
  have hstep3 : ∫ x in Set.Ioi (0 : ℝ), ∑ n ∈ Finset.Icc 1 N, c n * K n x =
      ∑ n ∈ Finset.Icc 1 N, c n * (1 / T) := by
    rw [integral_finsetSum _ (fun n hn => (hKint n hn).1.const_mul (c n))]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [integral_const_mul, (hKint n hn).2]
  have hstep4 : C * T ^ 2 * ∑ n ∈ Finset.Icc 1 N, c n * (1 / T) ≤
      16 * C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun n _ => ?_)
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hQ)
    have e : C * T ^ 2 * (c n * (1 / T)) = C * ((T * Q ^ 2 + 16 * n + 8 * T) * ‖a n‖ ^ 2) := by
      simp only [c]
      field_simp
      ring
    rw [e]
    have h1 : T * (Q : ℝ) ^ 2 + 16 * n + 8 * T ≤ 16 * ((Q : ℝ) ^ 2 * T + n) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖a n‖)) hC.le
    linarith
  calc _ ≤ _ := hstep1
    _ ≤ C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ∑ n ∈ Finset.Icc 1 N, c n * K n x :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = C * T ^ 2 * ∑ n ∈ Finset.Icc 1 N, c n * (1 / T) := by rw [hstep3]
    _ ≤ _ := hstep4

end GlobalTheory.HybridLargeSieve
