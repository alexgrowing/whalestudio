import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RconvSlice
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HtProj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HtCompact
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.DixmierMalliavin

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem dm_induction {K : Type} [Field K] [NumberField K] {n : ℕ}
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (P : TI K n → Prop) (h0 : P 0)
    (hc : ∀ β₁ β₂ : TI K n, SmoothT β₁ → P (conv ν β₁ β₂))
    (ha : ∀ β β' : TI K n, SmoothT β → SmoothT β' → P β → P β' → P (β + β'))
    (β : TI K n) (hβ : SmoothT β) : P β := by
  obtain ⟨N, φ, ψ, h, e⟩ := dixmierMalliavin (isExpLieAlgebra K n) ν (fun g => β g) hβ β.hasCompactSupport
  let _ := (isExpLieAlgebra K n).chartedSpace
  let a : Fin N → TI K n := fun i => ⟨⟨φ i, (h i).1.continuous⟩, (h i).2.1⟩
  let b : Fin N → TI K n := fun i => ⟨⟨ψ i, (h i).2.2.1.continuous⟩, (h i).2.2.2⟩
  have has : ∀ i, SmoothT (a i) := fun i => (h i).1
  have h0s : SmoothT (0 : TI K n) :=
    (isExpLieAlgebra K n).mem_smoothFuns.1 (Submodule.zero_mem _)
  have key : ∀ s : Finset (Fin N), SmoothT (∑ i ∈ s, conv ν (a i) (b i)) ∧ P (∑ i ∈ s, conv ν (a i) (b i)) ∧
      ∀ x, (∑ i ∈ s, conv ν (a i) (b i)) x = ∑ i ∈ s, groupConv ν (φ i) (ψ i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨by simpa using h0s, by simpa using h0, fun x => by simp⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hs := (UpperTheory.ConvolutionTheory.Tf.lactConv K n ν (a i) (b i) (has i)).1
      obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ hs
      refine ⟨(h6 _ ih.1).1, ha _ _ hs ih.1 (hc _ _ (has i)) ih.2.1, fun x => ?_⟩
      rw [Finset.sum_insert hi, CompactlySupportedContinuousMap.add_apply, ih.2.2, conv_apply]
      rfl
  have eβ : β = ∑ i, conv ν (a i) (b i) := by
    ext x
    rw [(key Finset.univ).2.2 x, ← Finset.sum_apply, ← e]
  rw [eβ]
  exact (key Finset.univ).2.1

private theorem lift_add {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (β β' : TI K n) (e : TF K n) (φ : LL μ) :
    liftOne (rconv (rationalGLOne K n) μ (tens (β + β') e) φ) =
      liftOne (rconv (rationalGLOne K n) μ (tens β e) φ) + liftOne (rconv (rationalGLOne K n) μ (tens β' e) φ) := by
  funext g
  rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).2.2.1 β']
  simp only [liftOne, Pi.add_apply, rconv]
  rw [← integral_add (integrable_rconv _ μ _ φ _) (integrable_rconv _ μ _ φ _)]
  simp only [CompactlySupportedContinuousMap.add_apply, add_mul]

private theorem lift_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (e : TF K n) (φ : LL μ) :
    liftOne (rconv (rationalGLOne K n) μ (tens (0 : TI K n) e) φ) = 0 := by
  have := lift_add hn μ 0 0 e φ
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem UpperTheory.liftOne_rconv_tensor_moderateGrowth_uniform :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], Compat μ ν m →
          ∀ (β : TI K n) (e : TF K n), SmoothT β → ∃ N : ℕ, ∀ u : UC K n, ∃ B : ℝ, ∀ (φ : LL μ) (g : AdelicGLn.AdelicGL K n),
            ‖liftOne (rconv (rationalGLOne K n) μ (tens (lact u β) e) φ) g‖ ≤ B * ‖φ‖ * AutomorphicForm.height g ^ N := by
  intro K _ _ n hn μ _ ν _ m _ hC β e hβ
  refine dm_induction ν (fun γ => ∃ N : ℕ, ∀ u : UC K n, ∃ B : ℝ, ∀ (φ : LL μ) (g : AdelicGLn.AdelicGL K n),
    ‖liftOne (rconv (rationalGLOne K n) μ (tens (lact u γ) e) φ) g‖ ≤ B * ‖φ‖ * AutomorphicForm.height g ^ N) ?_ ?_ ?_ β hβ
  · refine ⟨0, fun u => ⟨0, fun φ g => ?_⟩⟩
    have h0s : SmoothT (0 : TI K n) :=
      (isExpLieAlgebra K n).mem_smoothFuns.1 (Submodule.zero_mem _)
    obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ h0s
    have h := (h6 0 h0s).2 u
    rw [add_zero] at h
    rw [left_eq_add.1 h, lift_zero hn]
    simp
  · intro β₁ β₂ h₁
    obtain ⟨C, N, hCN⟩ := UpperTheory.ConvolutionTheory.C.polyBdAll K n μ (tens β₂ e)
    obtain ⟨D, c, hD, hDc⟩ := UpperTheory.ConvolutionTheory.Tf.htProj K n
    refine ⟨c * N, fun u => ?_⟩
    obtain ⟨_, -, hs, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ h₁
    obtain ⟨Y, hY, hYb, -⟩ := UpperTheory.ConvolutionTheory.Tf.htCompact K n
      ((fun a => (archP K n a : AdelicGLn.AdelicGL K n)) '' tsupport (lact u β₁))
      ((lact u β₁).hasCompactSupport.isCompact.image (continuous_subtype_val.comp continuous_archP))
    refine ⟨(∫ a, ‖lact u β₁ a‖ ∂ν) * (|C| * (heightConst K n * D * Y) ^ N), fun φ g => ?_⟩
    rw [(UpperTheory.ConvolutionTheory.Tf.lactConv K n ν β₁ β₂ h₁).2.1 u, liftOne,
      (UpperTheory.ConvolutionTheory.Tf.rconvSlice K n hn μ ν m hC (lact u β₁) β₂ e φ (hs u).1).1]
    have hint : Integrable (fun a => ‖lact u β₁ a‖) ν :=
      ((lact u β₁).continuous.integrable_of_hasCompactSupport (lact u β₁).hasCompactSupport).norm
    have hc1 : (1 : ℝ) ≤ heightConst K n := one_le_heightConst
    have hg := one_le_height g
    refine (norm_integral_le_of_norm_le (hint.mul_const
      (|C| * (heightConst K n * D * Y) ^ N * ‖φ‖ * AutomorphicForm.height g ^ (c * N)))
      (Filter.Eventually.of_forall fun a => ?_)).trans (by rw [integral_mul_const]; exact le_of_eq (by ring))
    rw [norm_mul]
    by_cases ha : lact u β₁ a = 0
    · simp [ha]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    set x : normOneGL K n := retractOne g * archP K n a with hx
    have hq0 : 0 ≤ PositivityTheory.Rg.Tf.Core.qht x := le_ciInf fun γ => (height_pos _).le
    have hq1 : PositivityTheory.Rg.Tf.Core.qht x ≤ AutomorphicForm.height (x : AdelicGLn.AdelicGL K n) := by
      refine (ciInf_le ⟨0, ?_⟩ 1).trans (le_of_eq (by simp))
      rintro _ ⟨γ, rfl⟩
      exact (height_pos _).le
    have hq2 : AutomorphicForm.height (x : AdelicGLn.AdelicGL K n) ≤
        heightConst K n * D * Y * AutomorphicForm.height g ^ c := by
      have h1 := height_mul_le (retractOne g : AdelicGLn.AdelicGL K n) (archP K n a : AdelicGLn.AdelicGL K n)
      have h2 := hYb _ ⟨a, subset_tsupport _ ha, rfl⟩
      refine h1.trans ((mul_le_mul (mul_le_mul_of_nonneg_left (hDc g) (by linarith)) h2 (height_pos _).le
        (by positivity)).trans (le_of_eq (by ring)))
    have h3 := pow_le_pow_left₀ hq0 (hq1.trans hq2) N
    rw [mul_pow, ← pow_mul] at h3
    refine (hCN φ x).trans ?_
    calc _ ≤ |C| * PositivityTheory.Rg.Tf.Core.qht x ^ N * ‖φ‖ := by
          first
            | exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hq0 N)) (norm_nonneg _)
            | (have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hq0 N)) (norm_nonneg φ); linarith)
      _ ≤ |C| * ((heightConst K n * D * Y) ^ N * AutomorphicForm.height g ^ (c * N)) * ‖φ‖ := by gcongr
      _ = _ := by ring
  · rintro γ γ' hγ hγ' ⟨N, hN⟩ ⟨N', hN'⟩
    refine ⟨max N N', fun u => ?_⟩
    obtain ⟨B, hB⟩ := hN u
    obtain ⟨B', hB'⟩ := hN' u
    refine ⟨|B| + |B'|, fun φ g => ?_⟩
    obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ hγ
    rw [(h6 γ' hγ').2 u, lift_add hn, Pi.add_apply]
    have hg := one_le_height g
    have k : ∀ (b : ℝ) (M : ℕ), M ≤ max N N' → b * ‖φ‖ * AutomorphicForm.height g ^ M ≤
        |b| * ‖φ‖ * AutomorphicForm.height g ^ max N N' := fun b M hM =>
      mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _)) (pow_le_pow_right₀ hg hM)
        (by positivity) (by positivity)
    refine (norm_add_le _ _).trans ((add_le_add ((hB φ g).trans (k B N (le_max_left _ _)))
      ((hB' φ g).trans (k B' N' (le_max_right _ _)))).trans (le_of_eq (by ring)))
