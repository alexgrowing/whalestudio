import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRealWhittakerInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableUnipotentFourierIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding

noncomputable section

open MeasureTheory
open Ad3 Ad3.LR Ad3.LR.C Ad3.LR.B

namespace GlobalTheory.CompanionTheory.PrimalInt

theorem measurable_Wm_comp {α : Type*} [MeasurableSpace α] (k : ℕ)
    (g : α → Matrix (Fin 2) (Fin 2) ℝ) (hg : ∀ i j, Measurable fun x => g x i j) :
    Measurable fun x => Wm k (g x) := by
  have hD : Measurable fun x => (g x).det := by
    simp only [Matrix.det_fin_two]
    exact ((hg 0 0).mul (hg 1 1)).sub ((hg 0 1).mul (hg 1 0))
  have e : ∀ i j, Measurable fun x => ((g x i j : ℝ) : ℂ) :=
    fun i j => Complex.measurable_ofReal.comp (hg i j)
  unfold Wm
  refine Measurable.ite (measurableSet_lt measurable_const hD) ?_ measurable_const
  have hden := (e 1 1).sub ((e 1 0).mul_const Complex.I)
  have hnum := (e 0 1).sub ((e 0 0).mul_const Complex.I)
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact Complex.measurable_ofReal.comp (hD.pow_const _)
  · exact hden.pow_const _
  · exact Complex.measurable_exp.comp ((hnum.div hden).const_mul _)

theorem measurable_val : Measurable (Units.val : ℝˣ → ℝ) :=
  GlobalTheory.CompanionTheory.TateR.val_measurableEmbedding.measurable

theorem measurable_chR (δ : Bool) (z : ℂ) : Measurable (chR δ z) := by
  unfold chR
  refine Measurable.mul (Measurable.ite ?_ measurable_const measurable_const) ?_
  · cases δ
    · simp
    · simpa using measurableSet_lt measurable_val measurable_const
  · exact (Complex.measurable_ofReal.comp measurable_val.abs).pow_const _

theorem measurable_inn (Φ : Sw) : Measurable fun h : M22 => inn Φ 1 (Matrix.of h) := by
  have := GlobalTheory.CompanionTheory.GodementInt.measurable_integral_mul_blk (⇑Φ) 1 Φ.continuous
  simpa [inn] using this

theorem innB_one (Φ : Sw) (h : M22) : innB (⇑Φ) h 1 = inn Φ 1 (Matrix.of h) := by
  simp [innB, inn]

theorem measurable_prI (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) : Measurable (prI k Φ δ s) := by
  unfold prI
  have hdet : Measurable fun p : ℝˣ × M22 => (Matrix.of p.2).det :=
    GlobalTheory.CompanionTheory.GodementWeight.measurable_det_of.comp measurable_snd
  have hW : Measurable fun p : ℝˣ × M22 => Wm k (d2 p.1 * (Matrix.of p.2)⁻¹) := by
    refine measurable_Wm_comp k _ fun i j => ?_
    have e : ∀ i j, Measurable fun p : ℝˣ × M22 =>
        ((Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) i j :=
      fun i j => (GlobalTheory.CompanionTheory.GodementWeight.measurable_inv_entry i j).comp measurable_snd
    have ha : Measurable fun p : ℝˣ × M22 => ((p.1 : ℝˣ) : ℝ) := measurable_val.comp measurable_fst
    fin_cases i
    · have hm : Measurable fun p : ℝˣ × M22 => ((p.1 : ℝˣ) : ℝ) *
          ((Matrix.of p.2)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 j := ha.mul (e 0 j)
      simpa [d2, Matrix.mul_apply, Fin.sum_univ_two] using hm
    · simpa [d2, Matrix.mul_apply, Fin.sum_univ_two] using e 1 j
  refine (((hW.mul ((measurable_inn Φ).comp measurable_snd)).mul
    (GlobalTheory.CompanionTheory.GodementWeight.measurable_sg hdet)).mul ?_).mul
    ((measurable_chR δ _).comp measurable_fst)
  exact Complex.measurable_ofReal.comp (hdet.abs.pow_const _)

theorem norm_sg (t : ℝ) : ‖sg t‖ = 1 := by
  unfold sg
  split_ifs <;> simp

theorem norm_chR (δ : Bool) (z : ℂ) (a : ℝˣ) : ‖chR δ z a‖ = |(a : ℝ)| ^ z.re := by
  have ha : 0 < |(a : ℝ)| := abs_pos.2 a.ne_zero
  unfold chR
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
  split_ifs <;> simp

theorem norm_prI (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) (a : ℝˣ) (h : M22) :
    ‖prI k Φ δ s (a, h)‖ = ‖inn Φ 1 (Matrix.of h)‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) *
      (‖Wm k (d2 a * (Matrix.of h)⁻¹)‖ * |(a : ℝ)| ^ (s.re - 1 / 2)) := by
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  unfold prI
  simp only [norm_mul, norm_sg, norm_chR, hre, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (Matrix.of h).det) _)]
  ring

theorem prI_of_det_zero (k : ℕ) (Φ : Sw) (δ : Bool) (s : ℂ) (a : ℝˣ) (h : M22)
    (hd : (Matrix.of h).det = 0) : prI k Φ δ s (a, h) = 0 := by
  have hinv : (Matrix.of h)⁻¹ = 0 := by
    apply Matrix.nonsing_inv_apply_not_isUnit
    rw [hd]
    simp
  simp [prI, hinv, Wm]

theorem inv_row (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -h 1 0 / (Matrix.of h).det ∧
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = h 0 0 / (Matrix.of h).det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp [Matrix.adjugate_fin_two, div_eq_inv_mul]

theorem det_power (A c2 σ : ℝ) (hA : 0 < A) (hc : 0 ≤ c2) :
    A ^ (-(1 : ℝ) / 2) * (A⁻¹ ^ (1 / 2 - σ) * (c2 / A ^ 2) ^ ((2 * σ - 1) / 2)) =
      A ^ (-σ) * c2 ^ ((2 * σ - 1) / 2) := by
  have h1 : A⁻¹ ^ (1 / 2 - σ) = A ^ (σ - 1 / 2) := by
    rw [Real.inv_rpow hA.le, ← Real.rpow_neg hA.le]
    congr 1
    ring
  have h2 : (A ^ 2) ^ ((2 * σ - 1) / 2) = A ^ (2 * σ - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    congr 1
    push_cast
    ring
  have h4 : (c2 / A ^ 2) ^ ((2 * σ - 1) / 2) = c2 ^ ((2 * σ - 1) / 2) * A ^ (-(2 * σ - 1)) := by
    rw [Real.div_rpow hc (by positivity), h2, Real.rpow_neg hA.le, div_eq_mul_inv]
  rw [h1, h4]
  have h3 : A ^ (-(1 : ℝ) / 2) * (A ^ (σ - 1 / 2) * (c2 ^ ((2 * σ - 1) / 2) * A ^ (-(2 * σ - 1)))) =
      (A ^ (-(1 : ℝ) / 2) * A ^ (σ - 1 / 2) * A ^ (-(2 * σ - 1))) * c2 ^ ((2 * σ - 1) / 2) := by ring
  rw [h3, ← Real.rpow_add hA, ← Real.rpow_add hA]
  congr 2
  ring

theorem col_le_eta (h : M22) (hd : (Matrix.of h).det ≠ 0) :
    1 + (h 0 0 ^ 2 + h 1 0 ^ 2) ^ ((1 : ℝ) / 2) / |(Matrix.of h).det| ≤ 2 * (1 + ‖eta h‖) := by
  obtain ⟨e0, e1⟩ := inv_row h hd
  have hA : 0 < |(Matrix.of h).det| := abs_pos.2 hd
  have b0 : |(Matrix.of h)⁻¹ 1 0| ≤ ‖eta h‖ := by
    simpa [eta] using norm_le_pi_norm (eta h) 0
  have b1 : |(Matrix.of h)⁻¹ 1 1| ≤ ‖eta h‖ := by
    simpa [eta] using norm_le_pi_norm (eta h) 1
  rw [e0, abs_div, abs_neg] at b0
  rw [e1, abs_div] at b1
  have hs : (h 0 0 ^ 2 + h 1 0 ^ 2) ^ ((1 : ℝ) / 2) ≤ |h 0 0| + |h 1 0| := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have := mul_nonneg (abs_nonneg (h 0 0)) (abs_nonneg (h 1 0))
    nlinarith [sq_abs (h 0 0), sq_abs (h 1 0)]
  have : (h 0 0 ^ 2 + h 1 0 ^ 2) ^ ((1 : ℝ) / 2) / |(Matrix.of h).det| ≤
      |h 0 0| / |(Matrix.of h).det| + |h 1 0| / |(Matrix.of h).det| := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hs hA.le
  linarith

theorem bound_of_det_ne (N : ℕ) (C K σ I E A c2 c1 nh : ℝ) (hA : 0 < A) (hc : 0 ≤ c2)
    (hnh : 0 ≤ nh) (hc1 : 1 ≤ c1) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hI : I ≤ K * A⁻¹ / ((1 + nh) ^ N * (1 + E) ^ N)) (hI0 : 0 ≤ I)
    (hcE : c1 ≤ 2 * (1 + E)) :
    I * A ^ (-(1 : ℝ) / 2) * (C * A⁻¹ ^ (1 / 2 - σ) * (c2 / A ^ 2) ^ ((2 * σ - 1) / 2)) ≤
      (|C| * K * 2 ^ N) * (A ^ (-1 - σ) * c2 ^ ((2 * σ - 1) / 2) / ((1 + nh) ^ N * c1 ^ N)) := by
  have hpow := det_power A c2 σ hA hc
  have hAs : A ^ (-1 - σ) = A⁻¹ * A ^ (-σ) := by
    rw [sub_eq_add_neg, Real.rpow_add hA, Real.rpow_neg_one]
  have hP : 0 ≤ A ^ (-σ) * c2 ^ ((2 * σ - 1) / 2) :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hc _)
  have hL : I * A ^ (-(1 : ℝ) / 2) * (C * A⁻¹ ^ (1 / 2 - σ) * (c2 / A ^ 2) ^ ((2 * σ - 1) / 2)) =
      C * I * (A ^ (-σ) * c2 ^ ((2 * σ - 1) / 2)) := by
    rw [← hpow]
    ring
  have hden : 1 / (1 + E) ^ N ≤ 2 ^ N / c1 ^ N := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hcE N
  have hI2 : I ≤ K * A⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N) := by
    refine hI.trans ?_
    have hn : 0 ≤ K * A⁻¹ / (1 + nh) ^ N := by positivity
    calc K * A⁻¹ / ((1 + nh) ^ N * (1 + E) ^ N)
        = K * A⁻¹ / (1 + nh) ^ N * (1 / (1 + E) ^ N) := by
          rw [div_mul_div_comm, mul_one]
      _ ≤ K * A⁻¹ / (1 + nh) ^ N * (2 ^ N / c1 ^ N) := mul_le_mul_of_nonneg_left hden hn
      _ = K * A⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N) := by rw [div_mul_div_comm]
  rw [hL, hAs]
  calc C * I * (A ^ (-σ) * c2 ^ ((2 * σ - 1) / 2))
      ≤ |C| * I * (A ^ (-σ) * c2 ^ ((2 * σ - 1) / 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hI0) hP
    _ ≤ |C| * (K * A⁻¹ * 2 ^ N / ((1 + nh) ^ N * c1 ^ N)) *
          (A ^ (-σ) * c2 ^ ((2 * σ - 1) / 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI2 (abs_nonneg C)) hP
    _ = _ := by ring

theorem main : IbpBound → AbsoluteZetaIntegralBound → ComplexMatrixMajorantIntegrable → PrimInt := by
  intro hIbp hAbs hM k hk Φ δ s hs0 hs1
  obtain ⟨C, hC⟩ := hAbs k hk s.re hs0 hs1
  obtain ⟨N, hN⟩ := hM s.re hs0 hs1
  have hMaj := hN N le_rfl
  obtain ⟨C₁, hC₁⟩ := hIbp N
  set B : ℝ := 2 ^ (N + 8) * (Finset.Iic ((N + 8, N) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ with hBdef
  have hB : ∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n (⇑Φ) X‖ ≤ B :=
    fun n hn X => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 8, N)) le_rfl hn Φ X
  have hInn : ∀ h : M22, (Matrix.of h).det ≠ 0 →
      ‖inn Φ 1 (Matrix.of h)‖ ≤ |C₁ * B| * |(Matrix.of h).det|⁻¹ /
        ((1 + ‖h‖) ^ N * (1 + ‖eta h‖) ^ N) := by
    intro h hd
    have := hC₁ (⇑Φ) B (Φ.smooth ⊤) hB h 1 hd
    rw [innB_one] at this
    refine this.trans ?_
    simp only [abs_one, one_mul]
    gcongr
    exact le_abs_self _
  have hmeas := measurable_prI k Φ δ s
  have hint : ∀ h : M22, ∀ a : ℝˣ, ‖prI k Φ δ s (a, h)‖ = ‖inn Φ 1 (Matrix.of h)‖ *
      |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) *
      (‖Wm k (d2 a * (Matrix.of h)⁻¹)‖ * |(a : ℝ)| ^ (s.re - 1 / 2)) :=
    fun h a => norm_prI k Φ δ s a h
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun h => ?_, ?_⟩
  · by_cases hd : (Matrix.of h).det = 0
    · simp only [prI_of_det_zero k Φ δ s _ h hd]
      exact integrable_zero _ _ _
    · have hdg : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
        exact inv_ne_zero hd
      refine Integrable.mono' (((hC _ hdg).1).const_mul
        (‖inn Φ 1 (Matrix.of h)‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2))) ?_ ?_
      · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun a => (hint h a).le
  · refine Integrable.mono' (hMaj.const_mul (|C| * |C₁ * B| * 2 ^ N)) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := mulR)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun h => ?_
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      by_cases hd : (Matrix.of h).det = 0
      · simp only [prI_of_det_zero k Φ δ s _ h hd, norm_zero, integral_zero]
        have : (0 : ℝ) ≤ |(Matrix.of h).det| ^ (-1 - s.re) *
            (h 0 0 ^ 2 + h 1 0 ^ 2) ^ ((2 * s.re - 1) / 2) /
            ((1 + ‖h‖) ^ N * (1 + (h 0 0 ^ 2 + h 1 0 ^ 2) ^ ((1 : ℝ) / 2) /
              |(Matrix.of h).det|) ^ N) := by positivity
        positivity
      · have hdg : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
          rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
          exact inv_ne_zero hd
        have hA : 0 < |(Matrix.of h).det| := abs_pos.2 hd
        have hdetinv : |((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det| =
            |(Matrix.of h).det|⁻¹ := by
          rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv]
        obtain ⟨e0, e1⟩ := inv_row h hd
        have hrow : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 +
            ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 =
            (h 0 0 ^ 2 + h 1 0 ^ 2) / |(Matrix.of h).det| ^ 2 := by
          rw [e0, e1, sq_abs]
          field_simp
          ring
        have hval : ∫ a : ℝˣ, ‖prI k Φ δ s (a, h)‖ ∂mulR = ‖inn Φ 1 (Matrix.of h)‖ *
            |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) *
            (C * |(Matrix.of h).det|⁻¹ ^ (1 / 2 - s.re) *
              ((h 0 0 ^ 2 + h 1 0 ^ 2) / |(Matrix.of h).det| ^ 2) ^ ((2 * s.re - 1) / 2)) := by
          simp only [hint h]
          rw [integral_const_mul, (hC _ hdg).2, hdetinv, hrow]
        rw [hval]
        refine bound_of_det_ne N C |C₁ * B| s.re _ ‖eta h‖ _ _ _ ‖h‖ hA (by positivity)
          (norm_nonneg _) ?_ (norm_nonneg _) (abs_nonneg _) (hInn h hd) (norm_nonneg _)
          (col_le_eta h hd)
        have : 0 ≤ (h 0 0 ^ 2 + h 1 0 ^ 2) ^ ((1 : ℝ) / 2) / |(Matrix.of h).det| := by positivity
        linarith

end GlobalTheory.CompanionTheory.PrimalInt
