import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GJHaar

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def ch (g : GL (Fin 2) F) : Fin 2 × Fin 2 → F := fun ij => (g : Matrix (Fin 2) (Fin 2) F) ij.1 ij.2

def rho (g : GL (Fin 2) F) : ℝ≥0∞ :=
  (((distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞)

def ent (r₂ : Fin 2 → F) (b a : F) : Fin 2 × Fin 2 → F := fun ij => (![![a, b], r₂] : Fin 2 → Fin 2 → F) ij.1 ij.2

theorem measurableEmbedding_ch : MeasurableEmbedding (ch : GL (Fin 2) F → Fin 2 × Fin 2 → F) :=
  (Measures.glChart F 2).isOpenEmbedding.measurableEmbedding

theorem rho_eq (g : GL (Fin 2) F) :
    rho g = (((modulus (g : Matrix (Fin 2) (Fin 2) F).det ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [rho, distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]

theorem measurable_rho : Measurable (rho : GL (Fin 2) F → ℝ≥0∞) := by
  have h : Continuous fun g : GL (Fin 2) F => modulus (g : Matrix (Fin 2) (Fin 2) F).det :=
    continuous_modulus.comp (Continuous.matrix_det Units.continuous_val)
  have h2 : Measurable fun g : GL (Fin 2) F => modulus (g : Matrix (Fin 2) (Fin 2) F).det :=
    h.measurable
  have : (rho : GL (Fin 2) F → ℝ≥0∞) = fun g : GL (Fin 2) F =>
      (((modulus (g : Matrix (Fin 2) (Fin 2) F).det ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) := funext rho_eq
  rw [this]
  exact ((h2.pow_const 2).inv).coe_nnreal_ennreal

theorem lintegral_hG (ψ : AddChar F Circle) (f : GL (Fin 2) F → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂LFS.hG ψ = ∫⁻ X, Function.extend ch (rho * f) 0 X
      ∂(Measure.pi fun _ : Fin 2 × Fin 2 => selfDualMeasure ψ) := by
  have he := measurableEmbedding_ch (F := F)
  set μ₄ : Measure (Fin 2 × Fin 2 → F) := Measure.pi fun _ : Fin 2 × Fin 2 => selfDualMeasure ψ
  have h1 : LFS.hG ψ = (μ₄.comap ch).withDensity rho := Measures.haarGL_eq F 2 μ₄
  rw [h1, lintegral_withDensity_eq_lintegral_mul _ measurable_rho hf]
  have h2 : ∫⁻ g, ((rho : GL (Fin 2) F → ℝ≥0∞) * f) g ∂(μ₄.comap ch) =
      ∫⁻ X, Function.extend ch ((rho : GL (Fin 2) F → ℝ≥0∞) * f) 0 X ∂(Measure.map ch (μ₄.comap ch)) := by
    rw [he.lintegral_map]
    exact lintegral_congr fun g => (he.injective.extend_apply _ _ g).symm
  rw [h2, he.map_comap, ← lintegral_indicator he.measurableSet_range]
  refine lintegral_congr fun X => ?_
  by_cases hX : X ∈ Set.range (ch : GL (Fin 2) F → _)
  · rw [Set.indicator_of_mem hX]
  · rw [Set.indicator_of_notMem hX, Function.extend_apply' _ _ _ (by simpa using hX)]
    rfl

theorem measurable_ent : Measurable fun p : (Fin 2 → F) × F × F => ent p.1 p.2.1 p.2.2 := by
  refine measurable_pi_iff.2 fun ij => ?_
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j
  · exact measurable_snd.snd
  · exact measurable_snd.fst
  · exact (measurable_pi_apply 0).comp measurable_fst
  · exact (measurable_pi_apply 1).comp measurable_fst

theorem map_ent (ψ : AddChar F Circle) :
    (Measure.pi fun _ : Fin 2 × Fin 2 => selfDualMeasure ψ) =
      Measure.map (fun p : (Fin 2 → F) × F × F => ent p.1 p.2.1 p.2.2)
        ((LFS.vol2 ψ).prod ((selfDualMeasure ψ).prod (selfDualMeasure ψ))) := by
  haveI : SigmaFinite (LFS.vol2 ψ) := by unfold LFS.vol2; infer_instance
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_ent (MeasurableSet.univ_pi hs)]
  have : (fun p : (Fin 2 → F) × F × F => ent p.1 p.2.1 p.2.2) ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ fun j => s (1, j)) ×ˢ (s (0, 1) ×ˢ s (0, 0)) := by
    ext ⟨r, b, a⟩
    simp [ent, Set.mem_pi, Prod.forall, Fin.forall_fin_two]
    tauto
  rw [this, Measure.prod_prod, Measure.prod_prod, LFS.vol2, Measure.pi_pi, Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  ring

theorem lintegral_ent (ψ : AddChar F Circle) (E : (Fin 2 × Fin 2 → F) → ℝ≥0∞) (hE : Measurable E) :
    ∫⁻ X, E X ∂(Measure.pi fun _ : Fin 2 × Fin 2 => selfDualMeasure ψ) =
      ∫⁻ r₂, ∫⁻ b, ∫⁻ a, E (ent r₂ b a) ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂LFS.vol2 ψ := by
  haveI : SigmaFinite (LFS.vol2 ψ) := by unfold LFS.vol2; infer_instance
  rw [map_ent, lintegral_map hE measurable_ent,
    lintegral_prod (fun p : (Fin 2 → F) × F × F => E (ent p.1 p.2.1 p.2.2))
      (hE.comp measurable_ent).aemeasurable]
  refine lintegral_congr fun r₂ => ?_
  rw [lintegral_prod (fun q : F × F => E (ent r₂ q.1 q.2))
    ((hE.comp measurable_ent).comp measurable_prodMk_left).aemeasurable]

theorem lintegral_subst (ψ : AddChar F Circle) {v : F} (hv : v ≠ 0) (u : F) (K : F → F → ℝ≥0∞) :
    ∫⁻ b, ∫⁻ a, K b a ∂selfDualMeasure ψ ∂selfDualMeasure ψ =
      ∫⁻ x, ∫⁻ y, K (x * v) (y / v + x * u) ∂selfDualMeasure ψ ∂selfDualMeasure ψ := by
  set μ := selfDualMeasure ψ
  have hvE : ((modulus v : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using modulus_ne_zero hv
  have hvT : ((modulus v : ℝ≥0) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have h1 : ∀ x, ∫⁻ y, K (x * v) (y / v + x * u) ∂μ = (modulus v : ℝ≥0∞) * ∫⁻ a, K (x * v) a ∂μ := by
    intro x
    have := lintegral_comp_mul_left μ (inv_ne_zero hv) (fun t => K (x * v) (t + x * u))
    simp only [modulus_inv] at this
    rw [ENNReal.coe_inv (modulus_ne_zero hv), inv_inv] at this
    rw [lintegral_add_right_eq_self (μ := μ) (fun t => K (x * v) t) (x * u)] at this
    rw [← this]
    refine lintegral_congr fun y => ?_
    rw [div_eq_inv_mul]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ hvT]
  have h2 := lintegral_comp_mul_left μ hv (fun b => ∫⁻ a, K b a ∂μ)
  simp only [mul_comm v] at h2
  rw [h2, ← mul_assoc, ENNReal.mul_inv_cancel hvE hvT, one_mul]

theorem hr_val {r : Fin 2 → F} (h : r 1 ≠ 0) :
    ((hr r : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(r 1)⁻¹, 0; r 0, r 1] := by
  have hd : (!![(r 1)⁻¹, 0; r 0, r 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    simp [Matrix.det_fin_two, h]
  unfold hr
  rw [dif_pos hd]
  rfl

theorem g_val (x : F) (y : Fˣ) {r : Fin 2 → F} (h : r 1 ≠ 0) :
    ((uni2 x * dg2 y 1 * hr r : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(y : F) / r 1 + x * r 0, x * r 1; r 0, r 1] := by
  rw [Units.val_mul, Units.val_mul, hr_val h]
  show (!![1, x; 0, 1] * !![(y : F), 0; 0, ((1 : Fˣ) : F)]) * _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]

theorem ch_g (x : F) (y : Fˣ) {r : Fin 2 → F} (h : r 1 ≠ 0) :
    ch (uni2 x * dg2 y 1 * hr r : GL (Fin 2) F) = ent r (x * r 1) ((y : F) / r 1 + x * r 0) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  rw [ch, g_val x y h]
  fin_cases i <;> fin_cases j <;> simp [ent]

theorem rho_g (x : F) (y : Fˣ) {r : Fin 2 → F} (h : r 1 ≠ 0) :
    rho (uni2 x * dg2 y 1 * hr r : GL (Fin 2) F) = ENNReal.ofReal ((modulus (y : F) : ℝ) ^ (-2 : ℤ)) := by
  rw [rho_eq, g_val x y h, Matrix.det_fin_two_of]
  have : ((y : F) / r 1 + x * r 0) * r 1 - x * r 1 * r 0 = y := by
    field_simp
    ring
  rw [this, ← ENNReal.ofReal_coe_nnreal]
  congr 1

theorem ent_not_range (x : F) {r : Fin 2 → F} (h : r 1 ≠ 0) :
    ¬ ∃ g : GL (Fin 2) F, ch g = ent r (x * r 1) ((0 : F) / r 1 + x * r 0) := by
  rintro ⟨g, hg⟩
  have hd : (g : Matrix (Fin 2) (Fin 2) F).det = 0 := by
    have h00 := congrFun hg (0, 0)
    have h01 := congrFun hg (0, 1)
    have h10 := congrFun hg (1, 0)
    have h11 := congrFun hg (1, 1)
    simp only [ch, ent] at h00 h01 h10 h11
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    simp
    ring
  exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero hd

open Classical in
theorem integrand_eq (f : GL (Fin 2) F → ℝ≥0∞) {r : Fin 2 → F} (h : r 1 ≠ 0) (x y : F) :
    Function.extend ch (rho * f) 0 (ent r (x * r 1) (y / r 1 + x * r 0)) =
      if h' : y = 0 ∨ r 1 = 0 then 0 else
        f (uni2 x * dg2 (Units.mk0 y (fun e => h' (Or.inl e))) 1 * hr r) *
          ENNReal.ofReal ((modulus y : ℝ) ^ (-2 : ℤ)) := by
  by_cases hy : y = 0
  · rw [dif_pos (Or.inl hy), hy, Function.extend_apply' _ _ _ (ent_not_range x h)]
    rfl
  · rw [dif_neg (not_or.2 ⟨hy, h⟩)]
    have := ch_g x (Units.mk0 y hy) h
    simp only [Units.val_mk0] at this
    rw [← this, (measurableEmbedding_ch (F := F)).injective.extend_apply, Pi.mul_apply, rho_g _ _ h,
      mul_comm]
    simp

theorem measure_zero_singleton (ψ : AddChar F Circle) : selfDualMeasure ψ {(0 : F)} = 0 := by
  set μ := selfDualMeasure ψ
  have hC : μ (valBall F 0) ≠ ∞ := (isCompact_valBall 0).measure_lt_top.ne
  have hq : ((residueCard F : ℝ≥0))⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_residueCard_nnreal
  have h : ∀ n : ℕ, μ {0} ≤ (((residueCard F : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ≥0∞) * μ (valBall F 0) := by
    intro n
    calc μ {0} ≤ μ (valBall F (n : ℤ)) := measure_mono (Set.singleton_subset_iff.2 (zero_mem _))
      _ = _ := by
        rw [measure_valBall μ (n : ℤ), _root_.zpow_neg, zpow_natCast, inv_pow]
  have ht : Filter.Tendsto (fun n : ℕ => (((residueCard F : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ≥0∞) * μ (valBall F 0))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (((residueCard F : ℝ≥0)⁻¹ ^ n : ℝ≥0) : ℝ≥0∞))
        Filter.atTop (nhds ((0 : ℝ≥0) : ℝ≥0∞)) :=
      ENNReal.tendsto_coe.2 (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
    have := ENNReal.Tendsto.mul_const h1 (Or.inr hC)
    simpa using this
  exact le_antisymm (ge_of_tendsto' ht h) (by simp)

instance nullSingleton (ψ : AddChar F Circle) : NullSingletonClass (selfDualMeasure ψ) :=
  ⟨fun x => by
    have h := measure_preimage_add_right (selfDualMeasure ψ) (-x) {(0 : F)}
    rw [measure_zero_singleton] at h
    have e : (fun h : F => h + -x) ⁻¹' {(0 : F)} = {x} := by
      ext y
      simp [add_neg_eq_zero]
    rwa [e] at h⟩

theorem ae_ne (ψ : AddChar F Circle) : ∀ᵐ r ∂LFS.vol2 ψ, r (1 : Fin 2) ≠ 0 := by
  have : LFS.vol2 ψ {r | r (1 : Fin 2) = 0} = 0 := by
    unfold LFS.vol2
    exact Measure.pi_hyperplane _ 1 0
  exact measure_eq_zero_iff_ae_notMem.1 this

theorem gjm1 : GJm1 := by
  intro F _ _ _ _ _ _ ψ _ f hf
  have hE : Measurable (Function.extend ch (rho * f) (0 : (Fin 2 × Fin 2 → F) → ℝ≥0∞)) :=
    measurableEmbedding_ch.measurable_extend (measurable_rho.mul hf) measurable_const
  rw [lintegral_hG ψ f hf, lintegral_ent ψ _ hE]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ne ψ] with r hr
  rw [lintegral_subst ψ hr (r 0) fun b a => Function.extend ch (rho * f) 0 (ent r b a)]
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  exact integrand_eq f hr x y

end GlobalTheory.CompanionTheory.GJHaar
