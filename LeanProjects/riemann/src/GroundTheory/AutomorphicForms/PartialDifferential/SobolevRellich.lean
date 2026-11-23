import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.SobolevInterpolation
import GroundTheory.AutomorphicForms.HilbertSchmidtKernel
import GroundTheory.AutomorphicForms.HilbertSchmidtCompact

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def cutoff (R : ℝ) : 𝓢(E, ℂ) :=
  let b : ContDiffBump (0 : E) := ⟨R.toNNReal + 1, R.toNNReal + 2, by positivity, by linarith⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : E → ℝ)) := b.hasCompactSupport.comp_left rfl
  have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ (b : E → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  h₁.toSchwartzMap h₂

theorem cutoff_eq_one {R : ℝ} {x : E} (hx : x ∈ Metric.ball (0 : E) (R + 1)) : cutoff R x = 1 := by
  simp only [cutoff]
  change ((ContDiffBump.toFun _ x : ℝ) : ℂ) = 1
  rw [Complex.ofReal_eq_one]
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall]
  rw [Metric.mem_ball] at hx
  simp only
  have : R ≤ R.toNNReal := Real.le_coe_toNNReal R
  linarith

theorem smulLeftCLM_cutoff_eq_self {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F']
    {R : ℝ} (u : 𝓢'(E, F')) (hu : Distribution.IsVanishingOn u (Metric.closedBall (0 : E) R)ᶜ) :
    smulLeftCLM F' (cutoff R : E → ℂ) u = u := by
  ext φ
  rw [smulLeftCLM_apply_apply]
  have h0 : u (SchwartzMap.smulLeftCLM ℂ (cutoff R : E → ℂ) φ - φ) = 0 := by
    apply hu
    have hsub : Function.support ⇑(SchwartzMap.smulLeftCLM ℂ (cutoff R : E → ℂ) φ - φ) ⊆
        (Metric.ball (0 : E) (R + 1))ᶜ := by
      intro x hx
      by_contra hb
      apply hx
      simp only [Set.mem_compl_iff, not_not] at hb
      rw [sub_apply, SchwartzMap.smulLeftCLM_apply_apply
        (cutoff R).hasTemperateGrowth, cutoff_eq_one hb, one_smul, sub_self]
    refine (closure_minimal hsub Metric.isOpen_ball.isClosed_compl).trans ?_
    intro x hx
    simp only [Set.mem_compl_iff, Metric.mem_ball, Metric.mem_closedBall, not_lt, not_le] at hx ⊢
    linarith
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem fourier_char_smul (χ : 𝓢(E, ℂ)) (η ξ : E) :
    𝓕 (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) ξ = (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by
  rw [Real.fourier_eq, SchwartzMap.fourier_coe, Real.fourier_eq]
  congr 1; ext x
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul, inner_sub_right]
  congr 3; ring

theorem fourierInv_smulLeft_fourier_apply (χ φ : 𝓢(E, ℂ)) (η : E) :
    (𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ)) : 𝓢(E, ℂ)) η =
      ∫ ξ, φ ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) := by
  have hg : Integrable (fun x : E ↦ (𝐞 (inner ℝ x η) : ℂ) * χ x) (volume : Measure E) := by
    refine (χ.integrable (μ := (volume : Measure E))).bdd_mul (c := 1) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact ae_of_all _ fun x ↦ (Circle.norm_coe _).le
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  have h := integral_fourier_smul_eq_of_integrable (F := ℂ) φ hg
  simp only [smul_eq_mul] at h
  simp_rw [fourier_char_smul] at h
  rw [← h]
  congr 1; ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, Circle.smul_def, smul_eq_mul,
    smul_eq_mul, SchwartzMap.fourier_coe]
  ring

section Kernel

variable (s N : ℝ) (χ : 𝓢(E, ℂ))

def rellichKernel (p : E × E) : ℂ :=
  weight (s - N) p.1 * (𝓕 χ : 𝓢(E, ℂ)) (p.1 - p.2) * weight (-s) p.2

variable {s N}

theorem continuous_rellichKernel : Continuous (rellichKernel (E := E) s N χ) := by
  unfold rellichKernel
  have h1 := (weight_hasTemperateGrowth (E := E) (s - N)).1.continuous
  have h2 := (weight_hasTemperateGrowth (E := E) (-s)).1.continuous
  fun_prop

theorem norm_rellichKernel_sq_le (ξ η : E) :
    ‖rellichKernel s N χ (ξ, η)‖ ^ 2 ≤
      2 ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (-N) *
        ((1 + ‖ξ - η‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2) := by
  have pξ : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have pη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have hp := peetre (-s) η ξ
  rw [abs_neg, norm_sub_rev η ξ] at hp
  simp only [rellichKernel, norm_mul, norm_weight, mul_pow]
  have e1 : ((1 + ‖ξ‖ ^ 2) ^ ((s - N) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (s - N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul pξ.le]; congr 1; push_cast; ring
  have e2 : ((1 + ‖η‖ ^ 2) ^ (-s / 2)) ^ 2 = (1 + ‖η‖ ^ 2) ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul pη.le]; congr 1; push_cast; ring
  rw [e1, e2]
  have e3 : (1 + ‖ξ‖ ^ 2) ^ (s - N) * (1 + ‖ξ‖ ^ 2) ^ (-s) = (1 + ‖ξ‖ ^ 2) ^ (-N) := by
    rw [← Real.rpow_add pξ]; congr 1; ring
  calc (1 + ‖ξ‖ ^ 2) ^ (s - N) * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2 * (1 + ‖η‖ ^ 2) ^ (-s)
      ≤ (1 + ‖ξ‖ ^ 2) ^ (s - N) * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2 *
          (2 ^ |s| * (1 + ‖ξ - η‖ ^ 2) ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (-s)) := by gcongr
    _ = 2 ^ |s| * ((1 + ‖ξ‖ ^ 2) ^ (s - N) * (1 + ‖ξ‖ ^ 2) ^ (-s)) *
          ((1 + ‖ξ - η‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η)‖ ^ 2) := by ring
    _ = _ := by rw [e3]

theorem integrable_weight_mul_norm_fourier_sq (s : ℝ) :
    Integrable (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2) (volume : Measure E) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  obtain ⟨C, hC⟩ := exists_norm_le_weight (𝓕 χ : 𝓢(E, ℂ)) (-(n + 1) / 2 - |s|)
  have hint := (integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := n + 1) (by linarith)).const_mul (C ^ 2)
  refine hint.mono' ?_ (ae_of_all _ fun ζ ↦ ?_)
  · have hc : Continuous (fun ζ : E ↦ (1 + ‖ζ‖ ^ 2) ^ |s|) :=
      (continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ζ ↦ Or.inl (by positivity : (0 : ℝ) < 1 + ‖ζ‖ ^ 2).ne'
    exact (hc.mul ((𝓕 χ : 𝓢(E, ℂ)).continuous.norm.pow 2)).aestronglyMeasurable
  · have pζ : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := hC ζ
    have h2 : ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2 ≤ (C * (1 + ‖ζ‖ ^ 2) ^ ((-(n + 1) / 2 - |s|) / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2
        ≤ (1 + ‖ζ‖ ^ 2) ^ |s| * (C * (1 + ‖ζ‖ ^ 2) ^ ((-(n + 1) / 2 - |s|) / 2)) ^ 2 := by
          gcongr
      _ = C ^ 2 * (1 + ‖ζ‖ ^ 2) ^ (-(n + 1) / 2) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + ‖ζ‖ ^ 2) ^ _), ← Real.rpow_mul pζ.le]
          rw [mul_left_comm, ← Real.rpow_add pζ]
          congr 2; push_cast; ring

theorem memLp_rellichKernel (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    MemLp (rellichKernel s N χ) 2 ((volume : Measure E).prod volume) := by
  have hmeas := (continuous_rellichKernel (s := s) (N := N) χ).aestronglyMeasurable
    (μ := (volume : Measure E).prod volume)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hH := integrable_weight_mul_norm_fourier_sq χ s
  have hW := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := 2 * N) hN
  have hW' : Integrable (fun ξ : E ↦ (1 + ‖ξ‖ ^ 2) ^ (-N)) (volume : Measure E) := by
    refine hW.congr (ae_of_all _ fun ξ ↦ ?_)
    simp only; congr 1; ring
  set H : E → ℝ := fun ζ ↦ (1 + ‖ζ‖ ^ 2) ^ |s| * ‖(𝓕 χ : 𝓢(E, ℂ)) ζ‖ ^ 2
  have hdom : Integrable (fun p : E × E ↦ 2 ^ |s| * (1 + ‖p.1‖ ^ 2) ^ (-N) * H (p.1 - p.2))
      ((volume : Measure E).prod volume) := by
    have hg := (hW'.const_mul (2 ^ |s|)).mul_prod (hH.comp_neg (μ := (volume : Measure E)))
    have hc := ((measurePreserving_prod_sub (volume : Measure E) (volume : Measure E)).integrable_comp
      hg.aestronglyMeasurable).2 hg
    refine hc.congr (ae_of_all _ fun p ↦ ?_)
    simp only [Function.comp_apply, neg_sub]
  refine hdom.mono' (hmeas.norm.pow 2) (ae_of_all _ fun p ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_rellichKernel_sq_le χ p.1 p.2

end Kernel

section Identity

variable {s N : ℝ} (χ : 𝓢(E, ℂ))

def rellichOp (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  L2Kernel.kernelOp ((memLp_rellichKernel (s := s) χ hN).toLp _)

theorem isCompactOperator_rellichOp (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    IsCompactOperator (rellichOp (s := s) χ hN) :=
  (L2Kernel.kernelOp_isHilbertSchmidt _).isCompactOperator

theorem rellichOp_apply_ae (hN : (Module.finrank ℝ E : ℝ) < 2 * N)
    (G : Lp ℂ 2 (volume : Measure E)) :
    rellichOp (s := s) χ hN G =ᵐ[volume] fun ξ ↦ ∫ η, rellichKernel s N χ (ξ, η) * G η :=
  L2Kernel.kernelOp_toLp_apply_ae (memLp_rellichKernel χ hN) G

theorem memLp_two_prod_mul (φ : 𝓢(E, ℂ)) (G : Lp ℂ 2 (volume : Measure E)) :
    MemLp (fun p : E × E ↦ φ p.1 * G p.2) 2 ((volume : Measure E).prod volume) := by
  have hφ := (φ.memLp 2 (volume : Measure E))
  have hG := Lp.memLp G
  have hm : AEStronglyMeasurable (fun p : E × E ↦ φ p.1 * G p.2)
      ((volume : Measure E).prod volume) :=
    (φ.continuous.aestronglyMeasurable.comp_fst).mul (hG.1.comp_snd)
  rw [memLp_two_iff_integrable_sq_norm hm]
  have h1 := (memLp_two_iff_integrable_sq_norm hφ.1).1 hφ
  have h2 := (memLp_two_iff_integrable_sq_norm hG.1).1 hG
  refine (h1.mul_prod h2).congr (ae_of_all _ fun p ↦ ?_)
  simp [mul_pow]

theorem fourier_bessel_inclusion_eq (hN : (Module.finrank ℝ E : ℝ) < 2 * N)
    (u : SobolevSpace E ℂ s)
    (hu : smulLeftCLM ℂ (χ : E → ℂ) (SobolevSpace.toDistribution u) = SobolevSpace.toDistribution u) :
    (𝓕 (SobolevSpace.bessel (s - N) (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) :
      Lp ℂ 2 (volume : Measure E)) = rellichOp (s := s) χ hN (𝓕 (SobolevSpace.bessel s u)) := by
  set G : Lp ℂ 2 (volume : Measure E) := 𝓕 (SobolevSpace.bessel s u)
  apply Lp.ext
  apply ae_eq_of_integral_schwartz_smul_eq (F := ℂ)
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  · exact (Lp.memLp _).locallyIntegrable (by norm_num)
  intro φ _
  set φ' : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ (weight (s - N)) φ
  set ψ : 𝓢(E, ℂ) := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ'))

  have hL : ∫ ξ, φ ξ • (𝓕 (SobolevSpace.bessel (s - N)
      (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) : Lp ℂ 2 (volume : Measure E)) ξ =
      ∫ η, (∫ ξ, φ' ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η)) * (weight (-s) η * G η) := by
    have e1 : ∫ ξ, φ ξ • (𝓕 (SobolevSpace.bessel (s - N)
        (SobolevSpace.inclusion (by linarith : s - N ≤ s) u)) : Lp ℂ 2 (volume : Measure E)) ξ =
        ∫ ξ, φ' ξ • fourierFun u ξ := by
      apply integral_congr_ae
      filter_upwards [fourierFun_inclusion (by linarith : s - N ≤ s) u] with ξ hξ
      rw [← weight_smul_fourierFun, hξ, SchwartzMap.smulLeftCLM_apply_apply
        (weight_hasTemperateGrowth _)]
      simp only [smul_eq_mul]; ring
    have e2 : SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) (𝓕 φ') = 𝓕 ψ := by
      simp only [ψ, FourierTransform.fourier_fourierInv_eq]
    rw [e1, ← fourier_apply_eq_integral, ← hu, TemperedDistribution.fourier_apply,
      smulLeftCLM_apply_apply, e2, ← TemperedDistribution.fourier_apply, fourier_apply_eq_integral]
    congr 1; ext η
    rw [fourierInv_smulLeft_fourier_apply, fourierFun, smul_eq_mul, smul_eq_mul]

  have hint : Integrable (fun p : E × E ↦ φ p.1 * rellichKernel s N χ p * G p.2)
      ((volume : Measure E).prod volume) := by
    have := (memLp_rellichKernel (s := s) χ hN).integrable_mul (memLp_two_prod_mul φ G)
    refine this.congr (ae_of_all _ fun p ↦ ?_)
    simp only [Pi.mul_apply]; ring
  have hR : ∫ ξ, φ ξ • (rellichOp (s := s) χ hN G : Lp ℂ 2 (volume : Measure E)) ξ =
      ∫ η, (∫ ξ, φ' ξ * (𝓕 χ : 𝓢(E, ℂ)) (ξ - η)) * (weight (-s) η * G η) := by
    have e1 : ∫ ξ, φ ξ • (rellichOp (s := s) χ hN G : Lp ℂ 2 (volume : Measure E)) ξ =
        ∫ ξ, ∫ η, φ ξ * rellichKernel s N χ (ξ, η) * G η := by
      apply integral_congr_ae
      filter_upwards [rellichOp_apply_ae (s := s) χ hN G] with ξ hξ
      rw [hξ, smul_eq_mul, ← integral_const_mul]
      congr 1; ext η; ring
    rw [e1, integral_integral_swap hint]
    congr 1; ext η
    rw [← integral_mul_const]
    congr 1; ext ξ
    simp only [rellichKernel, φ', SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth _),
      smul_eq_mul]
    ring
  rw [hL, hR]

end Identity

theorem norm_inclusion_sub_eq {s r : ℝ} (h : r ≤ s) (v w : SobolevSpace E ℂ s) :
    ‖SobolevSpace.inclusion h v - SobolevSpace.inclusion h w‖ =
      ‖(𝓕 (SobolevSpace.bessel r (SobolevSpace.inclusion h v)) : Lp ℂ 2 (volume : Measure E)) -
        𝓕 (SobolevSpace.bessel r (SobolevSpace.inclusion h w))‖ := by
  rw [SobolevSpace.norm_def, map_sub, ← Lp.norm_fourier_eq]
  congr 1
  exact (Lp.fourierTransformₗᵢ E ℂ).map_sub _ _

open Filter Topology in

theorem rellich {s t : ℝ} (hts : t < s) {K : Set E} (hK : IsCompact K)
    (u : ℕ → SobolevSpace E ℂ s) {M : ℝ} (hM : ∀ j, ‖u j‖ ≤ M)
    (hsupp : ∀ j, Distribution.IsVanishingOn (SobolevSpace.toDistribution (u j)) Kᶜ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : SobolevSpace E ℂ t,
      Tendsto (fun j ↦ SobolevSpace.inclusion hts.le (u (φ j))) atTop (𝓝 v) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  set χ := cutoff (E := E) R
  have hu : ∀ j, smulLeftCLM ℂ (χ : E → ℂ) (SobolevSpace.toDistribution (u j)) =
      SobolevSpace.toDistribution (u j) := fun j ↦
    smulLeftCLM_cutoff_eq_self _ ((hsupp j).mono (Set.compl_subset_compl.2 hR))
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  set N : ℝ := max n (s - t) + 1
  have hN : n < 2 * N := by
    have : n ≤ max n (s - t) := le_max_left _ _
    have hn : 0 ≤ n := Nat.cast_nonneg _
    linarith
  have hN0 : 0 ≤ N := by
    have : s - t ≤ max n (s - t) := le_max_right _ _
    linarith
  have hrt : s - N < t := by
    have : s - t ≤ max n (s - t) := le_max_right _ _
    linarith
  have hrs : s - N ≤ s := by linarith
  set T := rellichOp (s := s) χ hN
  set G : ℕ → Lp ℂ 2 (volume : Measure E) := fun j ↦ 𝓕 (SobolevSpace.bessel s (u j))
  set M' := max M 0
  have hG : ∀ j, G j ∈ Metric.closedBall (0 : Lp ℂ 2 (volume : Measure E)) M' := fun j ↦ by
    rw [Metric.mem_closedBall, dist_zero_right, Lp.norm_fourier_eq, ← SobolevSpace.norm_def]
    exact (hM j).trans (le_max_left _ _)
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompactOperator_rellichOp (s := s) χ hN).isCompact_closure_image_closedBall
    M' |>.tendsto_subseq (x := fun j ↦ T (G j)) fun j ↦ subset_closure ⟨G j, hG j, rfl⟩
  refine ⟨φ, hφ, ?_⟩

  have hC : CauchySeq (fun j ↦ T (G (φ j))) := hlim.cauchySeq
  have hdist : ∀ i j, dist (SobolevSpace.inclusion hrs (u (φ i)))
      (SobolevSpace.inclusion hrs (u (φ j))) = dist (T (G (φ i))) (T (G (φ j))) := by
    intro i j
    rw [dist_eq_norm, dist_eq_norm, norm_inclusion_sub_eq,
      fourier_bessel_inclusion_eq χ hN _ (hu _), fourier_bessel_inclusion_eq χ hN _ (hu _)]

  set θ := (s - t) / (s - (s - N))
  set α := (t - (s - N)) / (s - (s - N))
  have hθ : 0 < θ := div_pos (by linarith) (by linarith)
  have hα : 0 ≤ α := (div_pos (by linarith) (by linarith)).le
  have hinterp : ∀ i j, dist (SobolevSpace.inclusion hts.le (u (φ i)))
      (SobolevSpace.inclusion hts.le (u (φ j))) ≤
        (2 * M') ^ α * dist (T (G (φ i))) (T (G (φ j))) ^ θ := by
    intro i j
    have h := norm_inclusion_le_interpolation hrt hts (u (φ i) - u (φ j))
    rw [map_sub, map_sub] at h
    rw [dist_eq_norm, ← hdist, dist_eq_norm]
    refine h.trans ?_
    gcongr
    calc ‖u (φ i) - u (φ j)‖ ≤ ‖u (φ i)‖ + ‖u (φ j)‖ := norm_sub_le _ _
      _ ≤ M' + M' := add_le_add ((hM _).trans (le_max_left _ _)) ((hM _).trans (le_max_left _ _))
      _ = 2 * M' := by ring
  have hcauchy : CauchySeq (fun j ↦ SobolevSpace.inclusion hts.le (u (φ j))) := by
    rw [Metric.cauchySeq_iff] at hC ⊢
    intro ε hε
    set c := (2 * M') ^ α + 1
    have hc : 0 < c := by positivity
    obtain ⟨K₀, hK₀⟩ := hC ((ε / c) ^ (1 / θ)) (by positivity)
    refine ⟨K₀, fun i hi j hj ↦ ?_⟩
    have h1 := hK₀ i hi j hj
    have h2 : dist (T (G (φ i))) (T (G (φ j))) ^ θ < ε / c := by
      calc dist (T (G (φ i))) (T (G (φ j))) ^ θ < ((ε / c) ^ (1 / θ)) ^ θ :=
            Real.rpow_lt_rpow dist_nonneg h1 hθ
        _ = ε / c := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ.ne', Real.rpow_one]
    calc dist _ _ ≤ (2 * M') ^ α * dist (T (G (φ i))) (T (G (φ j))) ^ θ := hinterp i j
      _ ≤ c * dist (T (G (φ i))) (T (G (φ j))) ^ θ := by
          gcongr; linarith
      _ < c * (ε / c) := by gcongr
      _ = ε := by field_simp
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨v, hv⟩

end

end GroundTheory.Automorphic.Sobolev
