import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk

theorem lint_prod {I : Type} [Fintype I] [SigmaFinite (volume : Measure P)]
    (f : I → P → ℝ) (hf0 : ∀ v x, 0 ≤ f v x) (hm : ∀ v, Measurable (f v))
    (C : I → ℝ≥0) (hC : ∀ v, ∫⁻ x, ENNReal.ofReal (f v x) ≤ C v) :
    ∫⁻ w : I → P, ENNReal.ofReal (∏ v, f v (w v)) ≤ ((∏ v, C v : ℝ≥0) : ℝ≥0∞) := by
  have hint : ∀ v, Integrable (f v) := by
    intro v
    refine ⟨(hm v).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hf0 v))]
    exact lt_of_le_of_lt (hC v) ENNReal.coe_lt_top
  have hnn : ∀ w : I → P, 0 ≤ ∏ v, f v (w v) :=
    fun w => Finset.prod_nonneg fun v _ => hf0 v (w v)
  have hP : Integrable (fun w : I → P => ∏ v, f v (w v)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hP (ae_of_all _ hnn),
    integral_fintype_prod_volume_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg (hf0 v)), ENNReal.coe_finset_prod]
  refine Finset.prod_le_prod' fun v _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hint v) (ae_of_all _ (hf0 v))]
  exact hC v

theorem har1 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') (e : ℝ) (he : 0 ≤ e) :
    kap z w ^ e ≤ (8 : ℝ) ^ e * kap z w' ^ e := by
  unfold B1c at hB
  obtain ⟨h1, -, h3, -⟩ := hB
  have hzw := (h1 z w).1
  have hzw' := (h1 z w').1
  have key : kap z w ≤ 8 * kap z w' := by
    nlinarith [h3 z w w', mul_le_mul_of_nonneg_left h hzw]
  calc kap z w ^ e ≤ (8 * kap z w') ^ e := Real.rpow_le_rpow hzw key he
    _ = (8 : ℝ) ^ e * kap z w' ^ e := Real.mul_rpow (by norm_num) hzw'

theorem har2 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') :
    (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) := by
  unfold B1c at hB
  obtain ⟨-, -, -, h4, -⟩ := hB
  have hw : 0 < |w.1.im| := abs_pos.mpr w.2
  have hw' : 0 < |w'.1.im| := abs_pos.mpr w'.2
  have hz : 0 ≤ |z.1.im| := abs_nonneg _
  have hww : |w'.1.im| ≤ 8 * |w.1.im| := by
    nlinarith [h4 w w', mul_le_mul_of_nonneg_right h hw'.le]
  have key : |z.1.im| / |w.1.im| ≤ 8 * (|z.1.im| / |w'.1.im|) := by
    rw [mul_div_assoc', div_le_div_iff₀ hw hw']
    nlinarith [mul_le_mul_of_nonneg_left hww hz]
  calc (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 * (|z.1.im| / |w'.1.im|)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg hz hw.le) key (by norm_num)
    _ = (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (div_nonneg hz hw'.le)

theorem meas_abs_im : Measurable fun x : P => |x.1.im| := by
  exact (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable

end UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk.KappaIntegralLemmas in
theorem UpperTheory.Esk.pf_KapInt : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B6 → UpperTheory.Esk.KapInt := by
  intro hA _ hB h6
  unfold KapInt
  intro I _ k hk
  have hσ : SigmaFinite (volume : Measure P) := by
    unfold B1a at hA
    exact hA.1
  haveI := hσ
  have hB' := hB
  unfold B1c at hB'
  obtain ⟨h1, -, -, -, h5, -⟩ := hB'
  unfold B6 at h6
  choose Cv hCv using fun v => h6 (k v) (hk v)
  have ha : ∀ v, 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := fun v => by positivity
  have hA' : ((∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) : ℝ≥0) : ℝ)
      = ∏ v, (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [NNReal.coe_prod]
    exact Finset.prod_congr rfl fun v _ => Real.coe_toNNReal _ (ha v)
  refine ⟨∏ v, Cv v, ∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)), fun z => ?_⟩
  have hkm : ∀ v, Measurable (fun t : P => kap (z v) t) := fun v =>
    h5.measurable.comp (measurable_const.prodMk measurable_id)
  have hsplit : ∀ w : X I, Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
      = ∏ v, (kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) := by
    intro w
    rw [Finset.prod_mul_distrib]
    rfl
  refine ⟨?_, ?_, ?_, fun w w' hn => ⟨?_, ?_⟩⟩
  · unfold Kap
    exact Finset.measurable_prod _ fun v _ => ((hkm v).comp (measurable_pi_apply v)).pow_const _
  · unfold Kap
    exact lint_prod (fun v t => kap (z v) t ^ ((k v : ℝ) / 2))
      (fun v t => Real.rpow_nonneg (h1 _ _).1 _) (fun v => (hkm v).pow_const _) Cv
      (fun v => (hCv v (z v)).1)
  · simp only [hsplit]
    exact lint_prod
      (fun v t => kap (z v) t ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |t.1.im|) ^ ((1 : ℝ) / 2))
      (fun v t => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
        (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _))
      (fun v => ((hkm v).pow_const _).mul ((measurable_const.div meas_abs_im).pow_const _)) Cv
      (fun v => (hCv v (z v)).2)
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    unfold Kap
    rw [hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => Real.rpow_nonneg (h1 _ _).1 _) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hp : 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2)
        ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := e1
      _ ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left h8 hp]
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    rw [hsplit w, hsplit w', hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
      (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have e2 := har2 hB (z v) (w v) (w' v) (hn' v)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
        ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2)) *
            ((8 : ℝ) ^ ((1 : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul e1 e2 (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)
            (mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _))
      _ = ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) *
            (kap (z v) (w' v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) := by
        ring
