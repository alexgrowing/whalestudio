import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEBlockConv

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open GLnLocal MeasureTheory Measure GJMatrix ValuativeRel
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {m : ℕ} [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]

theorem IsSchwartzBruhat.integrable_matrix {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    Integrable Φ (matrixMeasure (n := Fin m) μ₁) :=
  hΦ.1.continuous.integrable_of_hasCompactSupport hΦ.2

theorem integrable_fourier_kernel {ψ : AddChar F Circle} (hψ : Continuous ψ)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (a b : Matrix (Fin m) (Fin m) F → Matrix (Fin m) (Fin m) F)
    (ha : Continuous a) (hb : Continuous b) (hbi : Integrable (fun X => Ψ (b X)) (matrixMeasure μ₁)) :
    Integrable (fun p : Matrix (Fin m) (Fin m) F × Matrix (Fin m) (Fin m) F =>
      Φ p.1 * ((ψ (Matrix.trace (a p.1 * p.2)) : Circle) : ℂ) * Ψ (b p.2))
      ((matrixMeasure (n := Fin m) μ₁).prod (matrixMeasure μ₁)) := by
  have hprod := (hΦ.integrable_matrix μ₁).mul_prod hbi
  refine hprod.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (((hΦ.1.continuous.comp continuous_fst).mul ((continuous_subtype_val.comp hψ).comp
      (Continuous.matrix_trace ((ha.comp continuous_fst).matrix_mul continuous_snd)))).mul
      ((hΨ.1.continuous.comp hb).comp continuous_snd)).aestronglyMeasurable
  · simp only [norm_mul, Circle.norm_coe, mul_one]
    rfl

theorem integral_fourier_mul {ψ : AddChar F Circle} (hψ : Continuous ψ)
    {f g : Matrix (Fin m) (Fin m) F → ℂ} (hf : IsSchwartzBruhat f) (hg : IsSchwartzBruhat g) :
    ∫ W, localMatrixFourier ψ f W * g W ∂matrixMeasure (LocalField.selfDualMeasure ψ) =
      ∫ Z, f Z * localMatrixFourier ψ g Z ∂matrixMeasure (LocalField.selfDualMeasure ψ) := by
  set M := matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)
  have hint := integrable_fourier_kernel hψ hf hg (LocalField.selfDualMeasure ψ) id id continuous_id
    continuous_id (hg.integrable_matrix _)
  simp only [id] at hint
  have h1 : ∫ W, localMatrixFourier ψ f W * g W ∂M = ∫ W, ∫ Z, f Z *
      ((ψ (Matrix.trace (Z * W)) : Circle) : ℂ) * g W ∂M ∂M := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only [localMatrixFourier]
    rw [← integral_mul_const]
  have h2 : ∫ Z, f Z * localMatrixFourier ψ g Z ∂M = ∫ Z, ∫ W, f Z *
      ((ψ (Matrix.trace (Z * W)) : Circle) : ℂ) * g W ∂M ∂M := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
    simp only [localMatrixFourier]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only
    rw [Matrix.trace_mul_comm W Z]
    ring
  rw [h1, h2, ← integral_prod_symm _ hint, integral_prod _ hint]

theorem localMatrixFourier_comp_mul_left {ψ : AddChar F Circle} (Φ : Matrix (Fin m) (Fin m) F → ℂ)
    (y : GL (Fin m) F) (W : Matrix (Fin m) (Fin m) F) :
    localMatrixFourier ψ (fun Z => Φ ((y : Matrix (Fin m) (Fin m) F) * Z)) W =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m)⁻¹ •
        localMatrixFourier ψ Φ (W * ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) := by
  have h := integral_comp_mul_left_matrix (LocalField.selfDualMeasure ψ) y
    (fun Z => Φ Z * ((ψ (Matrix.trace (Z * (W * ((y⁻¹ : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F)))) : Circle) : ℂ))
  have htr : ∀ Z : Matrix (Fin m) (Fin m) F, Matrix.trace ((y : Matrix (Fin m) (Fin m) F) * Z *
      (W * ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F))) = Matrix.trace (Z * W) := by
    intro Z
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  simp only [localMatrixFourier]
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only [htr]

theorem integral_fourier_mul_right {ψ : AddChar F Circle} (hψ : Continuous ψ)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    (y : GL (Fin m) F) :
    ∫ X, localMatrixFourier ψ Φ X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))
        ∂matrixMeasure (LocalField.selfDualMeasure ψ) =
      ∫ X, Φ ((y : Matrix (Fin m) (Fin m) F) * X) * localMatrixFourier ψ Ψ X
        ∂matrixMeasure (LocalField.selfDualMeasure ψ) := by
  set d : ℝ := (LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m with hd
  have hd0 : d ≠ 0 := pow_ne_zero _ (by
    exact_mod_cast (LocalField.modulus_ne_zero (det_ne_zero y)))

  have h1 := integral_comp_mul_right_matrix (LocalField.selfDualMeasure ψ) y⁻¹
    (fun X => localMatrixFourier ψ Φ X * Ψ (X * (y : Matrix (Fin m) (Fin m) F)))
  have hdinv : (LocalField.modulus ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m =
      d⁻¹ := by
    rw [hd, ← inv_pow]
    congr 1
    have hm := LocalField.modulus_mul ((y : Matrix (Fin m) (Fin m) F).det)
      ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      LocalField.modulus_one] at hm
    have h' : (LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) *
        (LocalField.modulus ((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det : ℝ) = 1 := by
      exact_mod_cast hm.symm
    exact eq_inv_of_mul_eq_one_right h'
  rw [hdinv, inv_inv] at h1
  have h2 : ∫ X, localMatrixFourier ψ Φ X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))
      ∂matrixMeasure (LocalField.selfDualMeasure ψ) =
      ∫ W, localMatrixFourier ψ (fun Z => Φ ((y : Matrix (Fin m) (Fin m) F) * Z)) W * Ψ W
        ∂matrixMeasure (LocalField.selfDualMeasure ψ) := by
    rw [← inv_smul_smul₀ hd0 (∫ X, _ ∂_), ← h1, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only
    rw [localMatrixFourier_comp_mul_left, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one, smul_mul_assoc]
  rw [h2, integral_fourier_mul hψ (hΦ.comp_mul_left y) hΨ]

theorem lintegral_comp_linearEquiv {ι : Type*} [Fintype ι] (μ₀ : Measure (ι → F))
    [μ₀.IsAddHaarMeasure] (L : (ι → F) ≃ₗ[F] (ι → F)) (f : (ι → F) → ℝ≥0∞) :
    ∫⁻ x, f (L x) ∂μ₀ = ((distribHaarChar (ι → F) L)⁻¹ : ℝ≥0) * ∫⁻ x, f x ∂μ₀ := by
  have hLc : Continuous L := L.toLinearMap.continuous_on_pi
  have hLic : Continuous L.symm := L.symm.toLinearMap.continuous_on_pi
  let e : (ι → F) ≃ₜ (ι → F) := ⟨L.toEquiv, hLc, hLic⟩
  have hmap : Measure.map L μ₀ = ((distribHaarChar (ι → F) L)⁻¹ : ℝ≥0) • μ₀ := by
    ext S hS
    rw [Measure.map_apply hLc.measurable hS, Measure.smul_apply]
    have h := distribHaarChar_mul μ₀ L⁻¹ S
    have hpre : (L : (ι → F) → (ι → F)) ⁻¹' S = L⁻¹ • S := by
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, LinearEquiv.smul_def]
      rfl
    rw [hpre, ← h, map_inv, ENNReal.smul_def, smul_eq_mul]
  have := e.measurableEmbedding.lintegral_map (μ := μ₀) f
  change ∫⁻ y, f y ∂(Measure.map L μ₀) = _ at this
  calc ∫⁻ x, f (L x) ∂μ₀ = ∫⁻ x, f (e x) ∂μ₀ := rfl
    _ = _ := by rw [← this, hmap, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]

theorem lintegral_comp_mul_right_matrix (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (y : GL (Fin m) F)
    (f : Matrix (Fin m) (Fin m) F → ℝ≥0∞) :
    ∫⁻ X, f (X * (y : Matrix (Fin m) (Fin m) F)) ∂matrixMeasure (n := Fin m) μ₁ =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det ^ m)⁻¹ : ℝ≥0) *
        ∫⁻ X, f X ∂matrixMeasure (n := Fin m) μ₁ := by
  have hmp := measurePreserving_matrixCoord (n := Fin m) μ₁
  have hemb := (Measures.entriesHomeomorph F m).measurableEmbedding
  have hconv : ∀ g : Matrix (Fin m) (Fin m) F → ℝ≥0∞, ∫⁻ X, g X ∂matrixMeasure (n := Fin m) μ₁ =
      ∫⁻ x, g ((Measures.entries F m).symm x) ∂(Measure.pi fun _ : Fin m × Fin m => μ₁) := fun g => by
    rw [← hmp.lintegral_comp_emb hemb]
    rfl
  rw [hconv, hconv]
  have h := lintegral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((Measures.glChart F m).right y) (fun x => f ((Measures.entries F m).symm x))
  have hR : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).right y x) =
      (Measures.entries F m).symm x * (y : Matrix (Fin m) (Fin m) F) := fun x => by
    simp [Measures.glChart]
  simp only [hR] at h
  rw [h]
  congr 2
  have hc := Measures.glChart_rightModulus F m y
  rw [Measures.LinearChart.rightModulus] at hc
  rw [hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]

theorem lintegral_comp_mul_left_matrix (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (y : GL (Fin m) F)
    (f : Matrix (Fin m) (Fin m) F → ℝ≥0∞) :
    ∫⁻ X, f ((y : Matrix (Fin m) (Fin m) F) * X) ∂matrixMeasure (n := Fin m) μ₁ =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det ^ m)⁻¹ : ℝ≥0) *
        ∫⁻ X, f X ∂matrixMeasure (n := Fin m) μ₁ := by
  have hmp := measurePreserving_matrixCoord (n := Fin m) μ₁
  have hemb := (Measures.entriesHomeomorph F m).measurableEmbedding
  have hconv : ∀ g : Matrix (Fin m) (Fin m) F → ℝ≥0∞, ∫⁻ X, g X ∂matrixMeasure (n := Fin m) μ₁ =
      ∫⁻ x, g ((Measures.entries F m).symm x) ∂(Measure.pi fun _ : Fin m × Fin m => μ₁) := fun g => by
    rw [← hmp.lintegral_comp_emb hemb]
    rfl
  rw [hconv, hconv]
  have h := lintegral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((Measures.glChart F m).left y) (fun x => f ((Measures.entries F m).symm x))
  have hL : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).left y x) =
      (y : Matrix (Fin m) (Fin m) F) * (Measures.entries F m).symm x := fun x => by
    simp [Measures.glChart]
  simp only [hL] at h
  rw [h]
  congr 2
  have hc := Measures.glChart_leftModulus F m y
  rw [Measures.LinearChart.leftModulus] at hc
  rw [hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]

theorem inv_modulus_det_pow (y : GL (Fin m) F) :
    (((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det ^ m)⁻¹ : ℝ≥0) : ℝ) =
      ((LocalField.residueCard F : ℝ) ^ m) ^ ordDet y := by
  rw [LocalField.modulus_of_ne_zero (det_ne_zero y)]
  push_cast
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_neg, ordDet]
  congr 1
  ring

theorem IsSchwartzBruhat.lintegral_lt_top {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∫⁻ X, ‖Φ X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ < ∞ :=
  (hΦ.integrable_matrix μ₁).2

theorem exists_bound_kernel₁ {Φ' Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ' : IsSchwartzBruhat Φ')
    (hΨ : IsSchwartzBruhat Ψ) (hΨK : ∃ K : Set (GL (Fin m) F), IsCompact K ∧
      ∀ X, Ψ X ≠ 0 → ∃ g ∈ K, (g : Matrix (Fin m) (Fin m) F) = X)
    (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ y : GL (Fin m) F,
      ∫⁻ X, ‖Φ' X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ ∂matrixMeasure (n := Fin m) μ₁ ≤
        B * ENNReal.ofReal (min 1 (((LocalField.residueCard F : ℝ) ^ m) ^ ordDet y)) := by
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ'.exists_bound
  obtain ⟨A, hA⟩ := hΦ'.exists_ordDet_ge
  obtain ⟨K, hK, hKΨ⟩ := hΨK
  obtain ⟨e₁, he₁⟩ := (hK.image isLocallyConstant_ordDet_GL.continuous).bddAbove
  set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hqm : 1 ≤ q ^ m := one_le_pow₀ hq.le
  set k₂ : ℤ := e₁ + m * A
  set C₁ : ℝ≥0∞ := ENNReal.ofReal BΦ * ∫⁻ X, ‖Ψ X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ with hC₁def
  have hC₁ : C₁ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΨ.lintegral_lt_top μ₁).ne
  clear_value C₁
  refine ⟨C₁ * ENNReal.ofReal ((q ^ m) ^ max k₂ 0), ENNReal.mul_ne_top hC₁ ENNReal.ofReal_ne_top,
    fun y => ?_⟩
  by_cases hy : k₂ < ordDet y
  ·
    have hz : ∀ X, ‖Φ' X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ = 0 := by
      intro X
      rw [enorm_eq_zero]
      by_contra hne
      have hΨne : Ψ (X * (y : Matrix (Fin m) (Fin m) F)) ≠ 0 := right_ne_zero_of_mul hne
      have hΦne : Φ' X ≠ 0 := left_ne_zero_of_mul hne
      obtain ⟨k, hk, hkX⟩ := hKΨ _ hΨne
      have hX : X = ((k * y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
        rw [Units.val_mul, hkX, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]
      rw [hX] at hΦne
      have h1 := hA _ hΦne
      rw [ordDet_mul, ordDet_inv] at h1
      have h2 := he₁ ⟨k, hk, rfl⟩
      omega
    simp [hz]
  · push Not at hy
    calc ∫⁻ X, ‖Φ' X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ ∂matrixMeasure (n := Fin m) μ₁
        ≤ ∫⁻ X, ENNReal.ofReal BΦ * ‖Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ
            ∂matrixMeasure (n := Fin m) μ₁ := by
          refine lintegral_mono fun X => ?_
          rw [enorm_mul, ← ofReal_norm]
          gcongr
          exact hBΦ X
      _ = C₁ * ENNReal.ofReal ((q ^ m) ^ ordDet y) := by
          rw [hC₁def, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_comp_mul_right_matrix μ₁ y (fun X => ‖Ψ X‖ₑ), ← inv_modulus_det_pow,
            ENNReal.ofReal_coe_nnreal]
          ring
      _ ≤ C₁ * ENNReal.ofReal ((q ^ m) ^ max k₂ 0) * ENNReal.ofReal (min 1 ((q ^ m) ^ ordDet y)) := by
          rw [mul_assoc]
          gcongr C₁ * ?_
          rw [← ENNReal.ofReal_mul (zpow_nonneg (by positivity) _)]
          refine ENNReal.ofReal_le_ofReal ?_
          by_cases h0 : ordDet y ≤ 0
          · rw [min_eq_right (zpow_le_one_of_nonpos₀ hqm h0)]
            exact le_mul_of_one_le_left (zpow_nonneg (by positivity) _) (one_le_zpow₀ hqm
              (le_max_right _ _))
          · push Not at h0
            rw [min_eq_left (one_le_zpow₀ hqm h0.le), mul_one]
            exact zpow_le_zpow_right₀ hqm (le_trans hy (le_max_left _ _))

theorem exists_bound_kernel₂ {Φ Ψ' : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (hΨ' : IsSchwartzBruhat Ψ') (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ y : GL (Fin m) F,
      ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ ≤
        B * ENNReal.ofReal (min 1 (((LocalField.residueCard F : ℝ) ^ m) ^ ordDet y)) := by
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ.exists_bound
  obtain ⟨BΨ, hBΨ0, hBΨ⟩ := hΨ'.exists_bound
  set q : ℝ := (LocalField.residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hqm : 1 ≤ q ^ m := one_le_pow₀ hq.le
  set C₂ : ℝ≥0∞ := ENNReal.ofReal BΨ * ∫⁻ X, ‖Φ X‖ₑ ∂matrixMeasure (n := Fin m) μ₁
  set C₃ : ℝ≥0∞ := ENNReal.ofReal BΦ * ∫⁻ X, ‖Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁
  have hC₂ : C₂ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΦ.lintegral_lt_top μ₁).ne
  have hC₃ : C₃ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hΨ'.lintegral_lt_top μ₁).ne
  refine ⟨max C₂ C₃, max_ne_top hC₂ hC₃, fun y => ?_⟩
  have h2 : ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ ≤
      C₂ * ENNReal.ofReal ((q ^ m) ^ ordDet y) := by
    calc _ ≤ ∫⁻ X, ENNReal.ofReal BΨ * ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X)‖ₑ
            ∂matrixMeasure (n := Fin m) μ₁ := by
          refine lintegral_mono fun X => ?_
          rw [enorm_mul, ← ofReal_norm (Ψ' X), mul_comm]
          gcongr
          exact hBΨ X
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_comp_mul_left_matrix μ₁ y (fun X => ‖Φ X‖ₑ), ← inv_modulus_det_pow,
            ENNReal.ofReal_coe_nnreal]
          ring
  have h3 : ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ ≤
      C₃ := by
    calc _ ≤ ∫⁻ X, ENNReal.ofReal BΦ * ‖Ψ' X‖ₑ ∂matrixMeasure (n := Fin m) μ₁ := by
          refine lintegral_mono fun X => ?_
          rw [enorm_mul, ← ofReal_norm (Φ _)]
          gcongr
          exact hBΦ _
      _ = C₃ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  by_cases h0 : (q ^ m) ^ ordDet y ≤ 1
  · rw [min_eq_right h0]
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · push Not at h0
    rw [min_eq_left h0.le, ENNReal.ofReal_one, mul_one]
    exact h3.trans (le_max_right _ _)

theorem detPow_mul_detPow (g : GL (Fin m) F) (a b : ℂ) : detPow g a * detPow g b = detPow g (a + b) := by
  have h : (absDet g : ℂ) ≠ 0 := by
    rw [absDet]
    exact_mod_cast LocalField.modulus_ne_zero (det_ne_zero g)
  rw [detPow, detPow, detPow, Complex.cpow_add _ _ h]

theorem enorm_detPow_natCast (g : GL (Fin m) F) :
    ‖detPow g (m : ℂ)‖ₑ = ((detModulusPow g : ℝ≥0) : ℝ≥0∞) := by
  rw [detPow_natCast, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal]

def shearLeft (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : G × G ≃ₜ G × G where
  toFun z := (z.1, z.1 * z.2)
  invFun z := (z.1, z.1⁻¹ * z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_fst.mul continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.inv.mul continuous_snd)

def shearRight (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : G × G ≃ₜ G × G where
  toFun z := (z.1 * z.2, z.2)
  invFun z := (z.1 * z.2⁻¹, z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := (continuous_fst.mul continuous_snd).prodMk continuous_snd
  continuous_invFun := (continuous_fst.mul continuous_snd.inv).prodMk continuous_snd

variable [NeZero m] {α : ℂ} {c : GL (Fin m) F → ℂ}

theorem integral_kernel_left (hc : IsCentralCoeff m α c) (μ : Measure (GL (Fin m) F))
    [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    (hΨK : ∃ K : Set (GL (Fin m) F), IsCompact K ∧
      ∀ X, Ψ X ≠ 0 → ∃ g ∈ K, (g : Matrix (Fin m) (Fin m) F) = X)
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖)
    {κ : ℝ≥0} (hκint : ∀ f : Matrix (Fin m) (Fin m) F → ℂ,
      ∫ g, f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) ∂μ =
        (κ : ℝ) • ∫ X, f X ∂matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ))
    (hκlint : ∀ f : Matrix (Fin m) (Fin m) F → ℝ≥0∞, Measurable f →
      ∫⁻ g, f (g : Matrix (Fin m) (Fin m) F) * (detModulusPow g : ℝ≥0∞) ∂μ =
        κ * ∫⁻ X, f X ∂matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)) :
    ∫ g, Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, localMatrixFourier ψ Φ (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) *
          c (h⁻¹ * g) ∂μ) ∂μ =
      ∫ y, detPow y s * c y * ((κ : ℝ) • ∫ X, localMatrixFourier ψ Φ X *
        Ψ (X * (y : Matrix (Fin m) (Fin m) F)) ∂matrixMeasure (n := Fin m)
          (LocalField.selfDualMeasure ψ)) ∂μ := by
  set M := matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)
  set Φh := localMatrixFourier ψ Φ with hΦhdef
  have hΦh : IsSchwartzBruhat Φh := hΦ.localMatrixFourier hψ hψ1
  set F₁ : GL (Fin m) F × GL (Fin m) F → ℂ := fun p =>
    Φh (p.1 : Matrix (Fin m) (Fin m) F) * detPow p.1 (m - s) *
      (Ψ (p.2 : Matrix (Fin m) (Fin m) F) * detPow p.2 s) * c (p.1⁻¹ * p.2) with hF₁
  have hT : MeasurePreserving (shearLeft (GL (Fin m) F)) (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_mul μ μ
  have hTe : MeasurableEmbedding (shearLeft (GL (Fin m) F)) := (shearLeft _).measurableEmbedding
  have hF₁T : ∀ p : GL (Fin m) F × GL (Fin m) F, F₁ (shearLeft _ p) =
      (Φh (p.1 : Matrix (Fin m) (Fin m) F) * Ψ ((p.1 : Matrix (Fin m) (Fin m) F) *
        (p.2 : Matrix (Fin m) (Fin m) F)) * detPow p.1 (m : ℂ)) * (detPow p.2 s * c p.2) := by
    intro p
    simp only [hF₁, shearLeft, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, inv_mul_cancel_left,
      Units.val_mul, detPow_mul]
    have hadd := detPow_mul_detPow p.1 ((m : ℂ) - s) s
    rw [sub_add_cancel] at hadd
    rw [← hadd]
    ring

  have hcontT : Continuous (F₁ ∘ shearLeft (GL (Fin m) F)) := by
    have : (F₁ ∘ shearLeft (GL (Fin m) F)) = fun p => (Φh (p.1 : Matrix (Fin m) (Fin m) F) *
        Ψ ((p.1 : Matrix (Fin m) (Fin m) F) * (p.2 : Matrix (Fin m) (Fin m) F)) *
        detPow p.1 (m : ℂ)) * (detPow p.2 s * c p.2) := funext hF₁T
    rw [this]
    exact (((hΦh.1.continuous.comp (Units.continuous_val.comp continuous_fst)).mul
      (hΨ.1.continuous.comp ((Units.continuous_val.comp continuous_fst).mul
        (Units.continuous_val.comp continuous_snd)))).mul
      ((continuous_detPow _).comp continuous_fst)).mul
      (((continuous_detPow _).comp continuous_snd).mul (hc.continuous.comp continuous_snd))
  obtain ⟨B₁, hB₁, hbound⟩ := exists_bound_kernel₁ hΦh hΨ hΨK (LocalField.selfDualMeasure ψ)
  have hlint : ∫⁻ p, ‖(F₁ ∘ shearLeft (GL (Fin m) F)) p‖ₑ ∂(μ.prod μ) < ∞ := by
    rw [lintegral_prod_symm _ hcontT.enorm.measurable.aemeasurable]
    have hin : ∀ y : GL (Fin m) F, ∫⁻ h, ‖(F₁ ∘ shearLeft (GL (Fin m) F)) (h, y)‖ₑ ∂μ =
        ‖c y * detPow y s‖ₑ * (κ * ∫⁻ X, ‖Φh X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ ∂M) := by
      intro y
      have e1 : ∀ h : GL (Fin m) F, ‖(F₁ ∘ shearLeft (GL (Fin m) F)) (h, y)‖ₑ =
          ‖Φh (h : Matrix (Fin m) (Fin m) F) * Ψ ((h : Matrix (Fin m) (Fin m) F) *
            (y : Matrix (Fin m) (Fin m) F))‖ₑ * (detModulusPow h : ℝ≥0∞) *
            ‖c y * detPow y s‖ₑ := fun h => by
        rw [Function.comp_apply, hF₁T, enorm_mul, enorm_mul, enorm_detPow_natCast, mul_comm (detPow y s)]
      simp only [e1]
      rw [lintegral_mul_const' _ _ enorm_ne_top,
        hκlint (fun X => ‖Φh X * Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ)
        ((hΦh.1.continuous.mul (hΨ.1.continuous.comp (continuous_id.mul continuous_const))).enorm.measurable)]
      ring
    simp only [hin]
    exact hc.lintegral_weight_lt_top μ (J := fun y => κ * ∫⁻ X, ‖Φh X *
      Ψ (X * (y : Matrix (Fin m) (Fin m) F))‖ₑ ∂M) (B := κ * B₁)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hB₁) (fun y => by
        rw [mul_assoc]
        gcongr
        exact hbound y) hs hs'
  have hF₁Ti : Integrable (F₁ ∘ shearLeft (GL (Fin m) F)) (μ.prod μ) :=
    ⟨hcontT.aestronglyMeasurable, hlint⟩
  have hF₁i : Integrable F₁ (μ.prod μ) := (hT.integrable_comp_emb hTe).1 hF₁Ti
  calc ∫ g, Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, Φh (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) * c (h⁻¹ * g) ∂μ) ∂μ
      = ∫ g, ∫ h, F₁ (h, g) ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [hF₁]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        simp only
        ring
    _ = ∫ p, F₁ p ∂(μ.prod μ) := (integral_prod_symm F₁ hF₁i).symm
    _ = ∫ p, F₁ (shearLeft (GL (Fin m) F) p) ∂(μ.prod μ) := (hT.integral_comp hTe F₁).symm
    _ = ∫ y, ∫ h, F₁ (shearLeft (GL (Fin m) F) (h, y)) ∂μ ∂μ := integral_prod_symm _ hF₁Ti
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hF₁T]
        rw [integral_mul_const, hκint (fun X => Φh X * Ψ (X * (y : Matrix (Fin m) (Fin m) F)))]
        ring

theorem integral_kernel_right (hc : IsCentralCoeff m α c) (μ : Measure (GL (Fin m) F))
    [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖)
    {κ : ℝ≥0} (hκint : ∀ f : Matrix (Fin m) (Fin m) F → ℂ,
      ∫ g, f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) ∂μ =
        (κ : ℝ) • ∫ X, f X ∂matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ))
    (hκlint : ∀ f : Matrix (Fin m) (Fin m) F → ℝ≥0∞, Measurable f →
      ∫⁻ g, f (g : Matrix (Fin m) (Fin m) F) * (detModulusPow g : ℝ≥0∞) ∂μ =
        κ * ∫⁻ X, f X ∂matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)) :
    ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, localMatrixFourier ψ Ψ (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) *
          c (g * h⁻¹) ∂μ) ∂μ =
      ∫ y, detPow y s * c y * ((κ : ℝ) • ∫ X, Φ ((y : Matrix (Fin m) (Fin m) F) * X) *
        localMatrixFourier ψ Ψ X ∂matrixMeasure (n := Fin m)
          (LocalField.selfDualMeasure ψ)) ∂μ := by
  have : μ.IsMulRightInvariant := Measures.isMulRightInvariant_GL F m μ
  set M := matrixMeasure (n := Fin m) (LocalField.selfDualMeasure ψ)
  set Ψh := localMatrixFourier ψ Ψ with hΨhdef
  have hΨh : IsSchwartzBruhat Ψh := hΨ.localMatrixFourier hψ hψ1
  set F₂ : GL (Fin m) F × GL (Fin m) F → ℂ := fun p =>
    Φ (p.1 : Matrix (Fin m) (Fin m) F) * detPow p.1 s *
      (Ψh (p.2 : Matrix (Fin m) (Fin m) F) * detPow p.2 (m - s)) * c (p.1 * p.2⁻¹) with hF₂
  have hT : MeasurePreserving (shearRight (GL (Fin m) F)) (μ.prod μ) (μ.prod μ) :=
    measurePreserving_mul_prod μ μ
  have hTe : MeasurableEmbedding (shearRight (GL (Fin m) F)) := (shearRight _).measurableEmbedding
  have hF₂T : ∀ p : GL (Fin m) F × GL (Fin m) F, F₂ (shearRight _ p) =
      (Φ ((p.1 : Matrix (Fin m) (Fin m) F) * (p.2 : Matrix (Fin m) (Fin m) F)) *
        Ψh (p.2 : Matrix (Fin m) (Fin m) F) * detPow p.2 (m : ℂ)) * (detPow p.1 s * c p.1) := by
    intro p
    simp only [hF₂, shearRight, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, mul_inv_cancel_right,
      Units.val_mul, detPow_mul]
    have hadd := detPow_mul_detPow p.2 s ((m : ℂ) - s)
    rw [add_sub_cancel] at hadd
    rw [← hadd]
    ring
  have hcontT : Continuous (F₂ ∘ shearRight (GL (Fin m) F)) := by
    have : (F₂ ∘ shearRight (GL (Fin m) F)) = fun p => (Φ ((p.1 : Matrix (Fin m) (Fin m) F) *
        (p.2 : Matrix (Fin m) (Fin m) F)) * Ψh (p.2 : Matrix (Fin m) (Fin m) F) *
        detPow p.2 (m : ℂ)) * (detPow p.1 s * c p.1) := funext hF₂T
    rw [this]
    exact (((hΦ.1.continuous.comp ((Units.continuous_val.comp continuous_fst).mul
        (Units.continuous_val.comp continuous_snd))).mul
      (hΨh.1.continuous.comp (Units.continuous_val.comp continuous_snd))).mul
      ((continuous_detPow _).comp continuous_snd)).mul
      (((continuous_detPow _).comp continuous_fst).mul (hc.continuous.comp continuous_fst))
  obtain ⟨B₂, hB₂, hbound⟩ := exists_bound_kernel₂ hΦ hΨh (LocalField.selfDualMeasure ψ)
  have hlint : ∫⁻ p, ‖(F₂ ∘ shearRight (GL (Fin m) F)) p‖ₑ ∂(μ.prod μ) < ∞ := by
    rw [lintegral_prod _ hcontT.enorm.measurable.aemeasurable]
    have hin : ∀ y : GL (Fin m) F, ∫⁻ h, ‖(F₂ ∘ shearRight (GL (Fin m) F)) (y, h)‖ₑ ∂μ =
        ‖c y * detPow y s‖ₑ * (κ * ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψh X‖ₑ ∂M) := by
      intro y
      have e1 : ∀ h : GL (Fin m) F, ‖(F₂ ∘ shearRight (GL (Fin m) F)) (y, h)‖ₑ =
          ‖Φ ((y : Matrix (Fin m) (Fin m) F) * (h : Matrix (Fin m) (Fin m) F)) *
            Ψh (h : Matrix (Fin m) (Fin m) F)‖ₑ * (detModulusPow h : ℝ≥0∞) *
            ‖c y * detPow y s‖ₑ := fun h => by
        rw [Function.comp_apply, hF₂T, enorm_mul, enorm_mul, enorm_detPow_natCast,
          mul_comm (detPow y s)]
      simp only [e1]
      rw [lintegral_mul_const' _ _ enorm_ne_top,
        hκlint (fun X => ‖Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψh X‖ₑ)
        (((hΦ.1.continuous.comp (continuous_const.mul continuous_id)).mul
          hΨh.1.continuous).enorm.measurable)]
      ring
    simp only [hin]
    exact hc.lintegral_weight_lt_top μ (J := fun y => κ * ∫⁻ X, ‖Φ ((y : Matrix (Fin m) (Fin m) F) *
      X) * Ψh X‖ₑ ∂M) (B := κ * B₂)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hB₂) (fun y => by
        rw [mul_assoc]
        gcongr
        exact hbound y) hs hs'
  have hF₂Ti : Integrable (F₂ ∘ shearRight (GL (Fin m) F)) (μ.prod μ) :=
    ⟨hcontT.aestronglyMeasurable, hlint⟩
  have hF₂i : Integrable F₂ (μ.prod μ) := (hT.integrable_comp_emb hTe).1 hF₂Ti
  calc ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, Ψh (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) * c (g * h⁻¹) ∂μ) ∂μ
      = ∫ g, ∫ h, F₂ (g, h) ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [hF₂]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        simp only
        ring
    _ = ∫ p, F₂ p ∂(μ.prod μ) := (integral_prod F₂ hF₂i).symm
    _ = ∫ p, F₂ (shearRight (GL (Fin m) F) p) ∂(μ.prod μ) := (hT.integral_comp hTe F₂).symm
    _ = ∫ y, ∫ h, F₂ (shearRight (GL (Fin m) F) (y, h)) ∂μ ∂μ := integral_prod _ hF₂Ti
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hF₂T]
        rw [integral_mul_const, hκint (fun X => Φ ((y : Matrix (Fin m) (Fin m) F) * X) * Ψh X)]
        ring

theorem integral_kernel_eq (hc : IsCentralCoeff m α c) (μ : Measure (GL (Fin m) F))
    [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (hΨ : IsSchwartzBruhat Ψ)
    (hΨK : ∃ K : Set (GL (Fin m) F), IsCompact K ∧
      ∀ X, Ψ X ≠ 0 → ∃ g ∈ K, (g : Matrix (Fin m) (Fin m) F) = X)
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖) :
    ∫ g, Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, localMatrixFourier ψ Φ (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) *
          c (h⁻¹ * g) ∂μ) ∂μ =
      ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        (∫ h, localMatrixFourier ψ Ψ (h : Matrix (Fin m) (Fin m) F) * detPow h (m - s) *
          c (g * h⁻¹) ∂μ) ∂μ := by
  obtain ⟨κ, -, hκint, hκlint⟩ := exists_integral_GL_eq μ (LocalField.selfDualMeasure ψ)
  rw [integral_kernel_left hc μ hψ hψ1 hΦ hΨ hΨK hs hs' hκint hκlint,
    integral_kernel_right hc μ hψ hψ1 hΦ hΨ hs hs' hκint hκlint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_fourier_mul_right hψ hΦ hΨ y]

end GodementJacquet

end GroundTheory.Automorphic
