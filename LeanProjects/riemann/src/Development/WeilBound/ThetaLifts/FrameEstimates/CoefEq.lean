import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem memLp_two_of_lintegral {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hm : AEStronglyMeasurable f μ) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤) : MemLp f 2 μ := by
  refine ⟨hm, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa using h.lt_top

theorem integral_sq_eq {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} (hm : AEStronglyMeasurable f μ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x‖ ^ 2) (Eventually.of_forall fun x => by positivity)
    (hm.norm.pow 2)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem polar_pt (a b : ℂ) : a * (starRingEnd ℂ) b =
    (1 / 4 : ℂ) * (((‖a + b‖ ^ 2 : ℝ) : ℂ) - ((‖a - b‖ ^ 2 : ℝ) : ℂ) +
      (Complex.I * ((‖a + Complex.I * b‖ ^ 2 : ℝ) : ℂ) - Complex.I * ((‖a - Complex.I * b‖ ^ 2 : ℝ) : ℂ))) := by
  simp only [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / 2 * Complex.I_mul_I

theorem polar_int {X : Type} [MeasurableSpace X] {μ : Measure X} {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, f x * (starRingEnd ℂ) (g x) ∂μ =
    (1 / 4 : ℂ) * (((∫⁻ x, ‖(f + g) x‖ₑ ^ 2 ∂μ).toReal : ℂ) - ((∫⁻ x, ‖(f - g) x‖ₑ ^ 2 ∂μ).toReal : ℂ) +
      (Complex.I * ((∫⁻ x, ‖(f + Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℂ) -
        Complex.I * ((∫⁻ x, ‖(f - Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℂ))) := by
  have h1 := hf.add hg
  have h2 := hf.sub hg
  have h3 := hf.add (hg.const_smul Complex.I)
  have h4 := hf.sub (hg.const_smul Complex.I)
  have I : ∀ {k : X → ℂ}, MemLp k 2 μ → Integrable (fun x => ((‖k x‖ ^ 2 : ℝ) : ℂ)) μ := fun hk =>
    ((memLp_two_iff_integrable_sq_norm hk.1).1 hk).ofReal
  rw [← integral_sq_eq h1.1, ← integral_sq_eq h2.1, ← integral_sq_eq h3.1, ← integral_sq_eq h4.1,
    ← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_complex_ofReal,
    ← integral_const_mul, ← integral_const_mul, ← integral_sub (I h1) (I h2),
    ← integral_sub ((I h3).const_mul _) ((I h4).const_mul _),
    ← integral_add, ← integral_const_mul]
  · exact integral_congr_ae (Eventually.of_forall fun x => polar_pt (f x) (g x))
  · exact (I h1).sub (I h2)
  · exact ((I h3).const_mul _).sub ((I h4).const_mul _)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem continuous_schA {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have := (GlobalTheory.WeilAdm.HaarSplit.continuous_comp_splitE F κ Φ hΦ).comp
    (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)
  simpa [Function.comp_def] using this

theorem lintegral_sq_schwartz_gen {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {m : MeasurableSpace V} (hB : BorelSpace V) (μ : Measure V) (hμ : μ.IsAddHaarMeasure) (f : SchwartzMap V ℂ) :
    ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  have := (f.memLp 2 μ).2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
  simpa using this.ne

open scoped Classical in
theorem lintegral_sq_schwartz (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) : ∫⁻ z, ‖f z‖ₑ ^ 2 ≠ ⊤ := by
  have h0 : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
  exact lintegral_sq_schwartz_gen Pi.borelSpace _ (GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ) f

open scoped Classical in

theorem memLp_two_schA (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    MemLp Φ 2 μ := by
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have hc : Continuous (pureA F f g) := continuous_schA (Submodule.subset_span ⟨f, g, hg, rfl⟩)
    obtain ⟨ν, hν, C, -, hC, -, -, h, -⟩ := GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds F κ g hg ⊤ isOpen_univ
    have hf := lintegral_sq_schwartz f
    have h0 : MemLp (pureA F f g) 2 ν :=
      memLp_two_of_lintegral hc.aestronglyMeasurable (ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hf) (h f))
    rw [Measure.isAddLeftInvariant_eq_smul μ ν]
    exact h0.smul_measure ENNReal.coe_ne_top
  | zero => exact MemLp.zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.const_smul c

theorem inner_eq_of_unit (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ φ ∈ schA F κ, T φ ∈ schA F κ) (hu : ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ)
    {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ) :
    ∫ x, T Φ x * (starRingEnd ℂ) (T Ψ x) ∂μ = ∫ x, Φ x * (starRingEnd ℂ) (Ψ x) ∂μ := by
  have hI := (schA F κ).smul_mem Complex.I hΨ
  rw [polar_int (memLp_two_schA μ (hp _ hΦ)) (memLp_two_schA μ (hp _ hΨ)),
    polar_int (memLp_two_schA μ hΦ) (memLp_two_schA μ hΨ), ← map_smul, ← map_add, ← map_sub, ← map_add, ← map_sub,
    hu _ (add_mem hΦ hΨ), hu _ (sub_mem hΦ hΨ), hu _ (add_mem hΦ hI), hu _ (sub_mem hΦ hI)]

theorem coefEq_of : CoefEq := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ Φ₁ h₁ Φ₂ h₂ g h z
  have hs := IsUWeilPair.isUSplitting hP.weil
  set w := mat g⁻¹ * z * (mat h⁻¹)ᵀ with hw
  have e : actAB (cA σ) (g, h) w = z := by
    have a : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1
    have b : (mat h⁻¹)ᵀ * (mat h)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show mat h * mat h⁻¹ = 1 from Units.mul_inv h.1, Matrix.transpose_one]
    change mat g * w * (mat h)ᵀ = z
    rw [hw, Matrix.mul_assoc (mat g⁻¹), ← Matrix.mul_assoc (mat g), a, Matrix.one_mul, Matrix.mul_assoc, b,
      Matrix.mul_one]
  have i := hs.impl (g, h) w Φ₁ h₁
  rw [e] at i
  have k := inner_eq_of_unit μ (om (g, h)) (hs.pres _) (hs.unit μ hμ _)
    (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std w Φ₁ h₁) h₂
  rw [i] at k
  exact k

end PositivityTheory.ThKEst

end
