import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.EllipticLocal

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem norm_symb0 {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (ξ : E) :
    ‖symb0 c w ξ‖ = (2 * Real.pi) ^ m * ‖prinSymb c w ξ‖ := by
  rw [symb0, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  norm_num

theorem exists_symb0_bounds {ι : Type*} [Fintype ι] {m : ℕ} (hm : 1 ≤ m) (c : ι → ℂ)
    (w : ι → Fin m → E) (hell : ∀ ξ : E, ξ ≠ 0 → prinSymb c w ξ ≠ 0) :
    ∃ cl Cu : ℝ, 0 < cl ∧ 0 ≤ Cu ∧ (∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖) ∧
      ∀ ξ, ‖symb0 c w ξ‖ ≤ Cu * ‖ξ‖ ^ m := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_pos_le_norm_prinSymb hm c w hell
  refine ⟨(2 * Real.pi) ^ m * c₀, (2 * Real.pi) ^ m * ∑ i, ‖c i‖ * ∏ j, ‖w i j‖, by positivity,
    by positivity, fun ξ ↦ ?_, fun ξ ↦ ?_⟩
  · rw [norm_symb0, mul_assoc]; gcongr; exact hlow ξ
  · rw [norm_symb0, mul_assoc]; gcongr; exact norm_prinSymb_le c w ξ

def bumpGR (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) : ContDiffBump x₀ := ⟨r, R, hr, hrR⟩

def bumpG (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) : 𝓢(E, ℂ) :=
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (bumpGR x₀ hr hrR : E → ℝ)) :=
    (bumpGR x₀ hr hrR).hasCompactSupport.comp_left rfl
  have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ (bumpGR x₀ hr hrR : E → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpGR x₀ hr hrR).contDiff
  h₁.toSchwartzMap h₂

theorem bumpG_apply (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (x : E) :
    bumpG x₀ hr hrR x = ((bumpGR x₀ hr hrR x : ℝ) : ℂ) := rfl

theorem bumpG_eq_one (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) {x : E}
    (hx : x ∈ Metric.closedBall x₀ r) : bumpG x₀ hr hrR x = 1 := by
  rw [bumpG_apply, (bumpGR x₀ hr hrR).one_of_mem_closedBall hx, Complex.ofReal_one]

theorem tsupport_bumpG (x₀ : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    tsupport (bumpG x₀ hr hrR : E → ℂ) ⊆ Metric.closedBall x₀ R := by
  have : (bumpG x₀ hr hrR : E → ℂ) = Complex.ofRealCLM ∘ (bumpGR x₀ hr hrR : E → ℝ) := rfl
  rw [this]
  refine (tsupport_comp_subset (g := Complex.ofRealCLM) (by simp) _).trans ?_
  rw [(bumpGR x₀ hr hrR).tsupport_eq]; rfl

theorem IsEllipticAt.exists_data {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}
    (hT : IsEllipticAt T m x₀) (hm : 1 ≤ m) :
    ∃ (n : ℕ) (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)),
      T = prinOp a w + N ∧ HasOrder N ((m : ℝ) - 1) ∧ IsLocal N ∧
      ∃ cl Cu : ℝ, 0 < cl ∧ 0 ≤ Cu ∧ (∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖) ∧
        ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m := by
  obtain ⟨n, a, w, N, hTeq, hN, hNl, hell⟩ := hT
  exact ⟨n, a, w, N, hTeq, hN, hNl, exists_symb0_bounds hm _ w hell⟩

theorem IsEllipticAt.exists_regularity_radius {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}
    (hT : IsEllipticAt T m x₀) (hm : 1 ≤ m) :
    ∃ δ > 0, ∀ (s : ℝ) (u : 𝓢'(E, ℂ)), MemSobolev s 2 u →
      (∃ ρ < δ, Distribution.IsVanishingOn u (Metric.closedBall x₀ ρ)ᶜ) →
      MemSobolev (s - m + 1) 2 (T u) → MemSobolev (s + 1) 2 u := by
  obtain ⟨n, a, w, N, rfl, hN, hNl, cl, Cu, hcl, hCu, hlow, hup⟩ := hT.exists_data hm
  obtain ⟨δ, hδ, hsmall⟩ := exists_small a w N x₀ hcl hCu hlow hup hm hN 1
  refine ⟨δ, hδ, fun s u hu ⟨ρ, hρ, hvan⟩ hTu ↦ ?_⟩
  obtain ⟨μ, hμ0, hμ1, hK⟩ := hsmall {s, s + 1}
  have hKs := (hK s (by simp)).1
  have hKs1 := (hK (s + 1) (by simp)).1
  set K := Qop a w x₀ μ 1 ∘L locM a w N x₀ hδ

  have hTu' : (prinOp a w + N) u = P0 a w x₀ u + locM a w N x₀ hδ u :=
    prinOp_add_apply_eq a w N x₀ hNl hδ hρ hvan
  have hid : u + K u = Qop a w x₀ μ 1 ((prinOp a w + N) u) + Rop a w x₀ μ 1 u := by
    have h1 := congrArg (fun A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) ↦ A u) (parametrix_comp_frozenOperator a w x₀ hμ0.le 1)
    simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply] at h1
    rw [hTu', map_add, h1]
    simp only [K, ContinuousLinearMap.comp_apply]
    abel
  have hz : MemSobolev (s + 1) 2 (Qop a w x₀ μ 1 ((prinOp a w + N) u) + Rop a w x₀ μ 1 u) := by
    have h1 := (opBound_Qop a w x₀ hcl hCu hlow hup hμ0.le hμ1 1 (s + 1)).memSobolev
      (u := (prinOp a w + N) u) (by convert hTu using 2; ring)
    have h2 := (opBound_Rop a w x₀ hcl hCu hlow hup hμ0 1 s).memSobolev hu
    refine h1.add (h2.mono ?_)
    have : (1 : ℝ) ≤ ((2 * m * 1 : ℕ) : ℝ) := by
      have : 1 ≤ 2 * m * 1 := by omega
      exact_mod_cast this
    linarith
  obtain ⟨v, hv, hvK⟩ := exists_add_eq_of_opBound hKs1 hz
  have hdiff : (u - v) + K (u - v) = 0 := by
    rw [map_sub, show u - v + (K u - K v) = (u + K u) - (v + K v) by abel, hid, hvK, sub_self]
  have h0 := eq_zero_of_add_eq_zero hKs (hu.sub (hv.mono (by linarith))) hdiff
  rw [sub_eq_zero] at h0
  rw [h0]; exact hv

theorem isVanishingOn_prinOp_add_sub {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E)
    (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (x₀ : E) {δ : ℝ} (hδ : 0 < δ) (u : 𝓢'(E, ℂ)) :
    Distribution.IsVanishingOn ((prinOp a w + N) u - (P0 a w x₀ u + locM a w N x₀ hδ u))
      (Metric.ball x₀ δ) := by
  have hb : ∀ z : 𝓢'(E, ℂ), Distribution.IsVanishingOn
      (z - smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) z) (Metric.ball x₀ δ) := fun z ↦ by
    have := isVanishingOn_smulLeftCLM_sub (bump x₀ hδ).hasTemperateGrowth
      (V := Metric.ball x₀ δ) (fun x hx ↦ bump_eq_one x₀ hδ (Metric.ball_subset_closedBall hx)) z
    have h2 := isVanishingOn_neg this
    rwa [neg_sub] at h2
  have e : (prinOp a w + N) u - (P0 a w x₀ u + locM a w N x₀ hδ u) =
      ∑ i, ((smulLeftCLM ℂ (a i : E → ℂ) (∂^{w i} u) -
          smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (smulLeftCLM ℂ (a i : E → ℂ) (∂^{w i} u))) -
        a i x₀ • (∂^{w i} u - smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (∂^{w i} u))) +
      (N u - smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (N u)) := by
    simp only [add_apply, locM, P0, prinOp, constOp, sum_apply, ContinuousLinearMap.comp_apply,
      smul_apply, iteratedLineDerivOpCLM_apply, locCoeff, smulLeftCLM_schwartz_sub_smul,
      smulLeftCLM_schwartz_mul, smul_sub]
    simp only [Finset.sum_sub_distrib]
    abel
  rw [e]
  have hsum : ∀ S : Finset (Fin n), Distribution.IsVanishingOn ((∑ i ∈ S,
      ((smulLeftCLM ℂ (a i : E → ℂ) (∂^{w i} u) -
          smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (smulLeftCLM ℂ (a i : E → ℂ) (∂^{w i} u))) -
        a i x₀ • (∂^{w i} u - smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (∂^{w i} u))) : 𝓢'(E, ℂ)))
      (Metric.ball x₀ δ) := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => simpa using isVanishingOn_zero _
    | insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact isVanishingOn_add (isVanishingOn_sub (hb _) (isVanishingOn_smul _ (hb _))) ih
  exact isVanishingOn_add (hsum _) (hb _)

theorem memSobolev_delta (x₀ : E) {t : ℝ} (ht : t < -(Module.finrank ℝ E : ℝ) / 2) :
    MemSobolev t 2 (TemperedDistribution.delta x₀ : 𝓢'(E, ℂ)) := by
  rw [memSobolev_iff_fourier]
  refine ⟨fun ξ ↦ ((𝐞 (-inner ℝ ξ x₀) : Circle) : ℂ), ?_, fun φ ↦ ?_⟩
  · have hint := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
      (r := -2 * t) (by linarith)
    have hmeas : AEStronglyMeasurable (fun ξ : E ↦ weight t ξ • ((𝐞 (-inner ℝ ξ x₀) : Circle) : ℂ))
        volume :=
      ((weight_hasTemperateGrowth (E := E) t).1.continuous.smul (by fun_prop)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    refine hint.congr (ae_of_all _ fun ξ ↦ ?_)
    simp only [smul_eq_mul, norm_mul, Circle.norm_coe, mul_one, norm_weight]
    rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (t / 2)) 2, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  · rw [TemperedDistribution.fourier_apply, TemperedDistribution.delta_apply,
      SchwartzMap.fourier_coe, Real.fourier_eq]
    congr 1; ext v
    rw [Circle.smul_def, smul_eq_mul, smul_eq_mul, mul_comm]

theorem exists_add_eq_of_opBound_lt {K : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hK : OpBound K s s c) {z : 𝓢'(E, ℂ)} (hz : MemSobolev s 2 z) :
    ∃ v, MemSobolev s 2 v ∧ v + K v = z := by
  have hmem : ∀ v : SobolevSpace E ℂ s, MemSobolev s 2 (z - K (SobolevSpace.toDistribution v)) :=
    fun v ↦ (SobolevSpace.exists_toDistribution_eq_iff _).1
      ⟨SobolevSpace.mk z hz - SobolevSpace.mk _ (hK.memSobolev (SobolevSpace.memSobolev_toDistribution v)),
        by simp⟩
  let f : SobolevSpace E ℂ s → SobolevSpace E ℂ s := fun v ↦ SobolevSpace.mk _ (hmem v)
  have hf : ContractingWith c.toNNReal f := by
    refine ⟨by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0]; exact hc1,
      LipschitzWith.of_dist_le_mul fun v v' ↦ ?_⟩
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc0]
    have e : f v - f v' = SobolevSpace.mk (K (SobolevSpace.toDistribution (v' - v)))
        (hK.memSobolev (SobolevSpace.memSobolev_toDistribution _)) := by
      apply SobolevSpace.toDistribution_injective
      simp [f, map_sub]
    rw [e]
    have h := hK _ (SobolevSpace.memSobolev_toDistribution (v' - v))
    rw [sob_of_mem (hK.memSobolev (SobolevSpace.memSobolev_toDistribution _)), sob_toDistribution,
      ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hc0] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    rw [norm_sub_rev] at h'
    exact h'
  obtain ⟨v, hv⟩ : ∃ v, f v = v := ⟨_, hf.fixedPoint_isFixedPt (f := f)⟩
  refine ⟨SobolevSpace.toDistribution v, SobolevSpace.memSobolev_toDistribution v, ?_⟩
  have := congrArg SobolevSpace.toDistribution hv
  simp only [f, SobolevSpace.toDistribution_mk] at this
  exact eq_sub_iff_add_eq.1 this.symm

theorem OpBound.neg {A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s t C : ℝ} (h : OpBound A s t C) :
    OpBound (-A) s t C := fun u hu ↦ by rw [neg_apply, sob_neg]; exact h u hu

theorem OpBound.sub {A B : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s t C D : ℝ} (hA : OpBound A s t C)
    (hB : OpBound B s t D) (hC : 0 ≤ C) (hD : 0 ≤ D) : OpBound (A - B) s t (C + D) := by
  rw [sub_eq_add_neg]; exact hA.add hB.neg hC hD

theorem lintegral_mul_le_eLpNorm_mul (f g : E → ℂ) (hf : AEMeasurable (fun x ↦ ‖f x‖ₑ) volume)
    (hg : AEMeasurable (fun x ↦ ‖g x‖ₑ) volume) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have h := L2Kernel.lintegral_mul_sq_le (volume : Measure E) hf hg
  rw [← L2Kernel.eLpNorm_two_sq, ← L2Kernel.eLpNorm_two_sq, ← mul_pow] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem norm_ofSchwartz_smulLeft_fourierMultiplier_le (χ : 𝓢(E, ℂ)) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (t : ℝ) (hA : MemLp (weight t : E → ℂ) 2 volume)
    (hB : MemLp (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume) (φ : 𝓢(E, ℂ)) :
    ‖SobolevSpace.ofSchwartz t (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ)
        (SchwartzMap.fourierMultiplierCLM ℂ g φ))‖ ≤
      ((∫ x, ‖χ x‖) * (eLpNorm (weight t : E → ℂ) 2 volume).toReal *
        (eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume).toReal) * ‖SobolevSpace.ofSchwartz t φ‖ := by
  set ψ := SchwartzMap.fourierMultiplierCLM ℂ g φ
  have hψ : ∀ η, (𝓕 ψ : 𝓢(E, ℂ)) η = (g η * weight (-t) η) * (weight t η * (𝓕 φ : 𝓢(E, ℂ)) η) := by
    intro η
    rw [show ψ = SchwartzMap.fourierMultiplierCLM ℂ g φ from rfl,
      SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
      SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
    have : weight (-t) η * weight t η = 1 := by
      rw [weight_mul_weight, neg_add_cancel]; simp [weight]
    calc g η * (𝓕 φ : 𝓢(E, ℂ)) η = g η * (weight (-t) η * weight t η) * (𝓕 φ : 𝓢(E, ℂ)) η := by
          rw [this, mul_one]
      _ = _ := by ring
  set Cst : ℝ≥0∞ := ENNReal.ofReal (∫ x, ‖χ x‖) * eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume *
    eLpNorm (fun ξ ↦ weight t ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume
  have hCst : Cst ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB.eLpNorm_ne_top)
    (eLpNorm_weight_fourier_lt_top t φ).ne
  have hpt : ∀ ξ, ‖weight t ξ * (𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) ψ) : 𝓢(E, ℂ)) ξ‖ₑ ≤
      ‖(Cst.toReal : ℂ) * weight t ξ‖ₑ := by
    intro ξ
    rw [enorm_mul, enorm_mul, fourier_smulLeftCLM_apply, ← ofReal_norm (Cst.toReal : ℂ),
      Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCst,
      mul_comm Cst]
    gcongr
    calc ‖∫ η, (𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * (𝓕 ψ : 𝓢(E, ℂ)) η‖ₑ
        ≤ ∫⁻ η, ‖(𝓕 χ : 𝓢(E, ℂ)) (ξ - η) * (𝓕 ψ : 𝓢(E, ℂ)) η‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ η, ENNReal.ofReal (∫ x, ‖χ x‖) * (‖g η * weight (-t) η‖ₑ *
            ‖weight t η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ) := by
          refine lintegral_mono fun η ↦ ?_
          rw [enorm_mul, hψ, enorm_mul]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_fourier_le_integral χ _)
      _ = ENNReal.ofReal (∫ x, ‖χ x‖) * ∫⁻ η, ‖g η * weight (-t) η‖ₑ *
            ‖weight t η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (∫ x, ‖χ x‖) * (eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume *
            eLpNorm (fun ξ ↦ weight t ξ * (𝓕 φ : 𝓢(E, ℂ)) ξ) 2 volume) := by
          gcongr
          exact lintegral_mul_le_eLpNorm_mul _ _ hB.1.enorm
            (measurable_weight_mul_fourier t φ).enorm.aemeasurable
      _ = Cst := by rw [← mul_assoc]
  have hle := eLpNorm_mono_enorm hpt (p := 2) (μ := (volume : Measure E))
  rw [show (fun ξ ↦ (Cst.toReal : ℂ) * weight t ξ) = (Cst.toReal : ℂ) • (weight t : E → ℂ) from rfl,
    eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hCst] at hle
  rw [norm_ofSchwartz_eq, norm_ofSchwartz_eq]
  calc _ ≤ (Cst * eLpNorm (weight t : E → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hCst hA.eLpNorm_ne_top) hle
    _ = _ := by
        simp only [Cst, ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun x ↦ norm_nonneg _)]
        ring

theorem opBound_smulLeft_fourierMultiplier (χ : 𝓢(E, ℂ)) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (t : ℝ) (hA : MemLp (weight t : E → ℂ) 2 volume)
    (hB : MemLp (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume) :
    OpBound (smulLeftCLM ℂ (χ : E → ℂ) ∘L fourierMultiplierCLM ℂ g) t t
      ((∫ x, ‖χ x‖) * (eLpNorm (weight t : E → ℂ) 2 volume).toReal *
        (eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume).toReal) := by
  intro u hu
  refine sob_le_of_schwartz _ (by positivity) (fun φ ↦ ?_) hu
  rw [ContinuousLinearMap.comp_apply, fourierMultiplierCLM_toTemperedDistributionCLM_eq hg,
    smulLeftCLM_coe, sob_ofSchwartz, sob_ofSchwartz, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (norm_ofSchwartz_smulLeft_fourierMultiplier_le χ hg t hA hB φ)

theorem integral_norm_bump_le (x₀ : E) {r : ℝ} (hr : 0 < r) :
    ∫ x, ‖bump x₀ hr x‖ ≤ volume.real (Metric.closedBall x₀ (2 * r)) := by
  rw [← integral_indicator_one Metric.isClosed_closedBall.measurableSet]
  refine integral_mono (bump x₀ hr).integrable.norm ?_ fun x ↦ ?_
  · exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (measure_closedBall_lt_top).ne)
  · by_cases hx : x ∈ Metric.closedBall x₀ (2 * r)
    · rw [Set.indicator_of_mem hx]; exact norm_bump_le x₀ hr x
    · rw [Set.indicator_of_notMem hx, bump_eq_zero x₀ hr hx, norm_zero]

theorem exists_bump_small [Nontrivial E] (x₀ : E) {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀) :
    ∃ r, ∃ hr : 0 < r, r ≤ r₀ ∧ (∫ x, ‖bump x₀ hr x‖) * C ≤ 1 / 4 := by
  set V := volume.real (Metric.ball (0 : E) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  set r := min r₀ (min (1 / 2) (1 / (8 * (C + 1) * (V + 1))))
  have hr : 0 < r := lt_min hr₀ (lt_min (by norm_num) (by positivity))
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  have hr2 : 2 * r ≤ 1 := by
    have : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hr3 : r ≤ 1 / (8 * (C + 1) * (V + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
  have hvol : volume.real (Metric.closedBall x₀ (2 * r)) ≤ 2 * r * V := by
    rw [Measure.addHaar_real_closedBall _ _ (by linarith)]
    gcongr
    calc (2 * r) ^ Module.finrank ℝ E ≤ (2 * r) ^ 1 := pow_le_pow_of_le_one (by linarith) hr2 hn
      _ = 2 * r := pow_one _
  calc (∫ x, ‖bump x₀ hr x‖) * C ≤ (2 * r * V) * C := by
        gcongr; exact (integral_norm_bump_le x₀ hr).trans hvol
    _ ≤ (2 * (1 / (8 * (C + 1) * (V + 1))) * V) * C := by gcongr
    _ = (1 / 4) * ((V / (V + 1)) * (C / (C + 1))) := by field_simp; ring
    _ ≤ (1 / 4) * (1 * 1) := by
        gcongr
        · rw [div_le_one (by linarith)]; linarith
        · rw [div_le_one (by linarith)]; linarith
    _ = 1 / 4 := by ring

theorem memLp_weight {t : ℝ} (ht : t < -(Module.finrank ℝ E : ℝ) / 2) :
    MemLp (weight t : E → ℂ) 2 volume := by
  have hint := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := -2 * t) (by linarith)
  have hmeas : AEStronglyMeasurable (weight t : E → ℂ) volume :=
    (weight_hasTemperateGrowth (E := E) t).1.continuous.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hint.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only [norm_weight]
  rw [← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (t / 2)) 2, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

theorem memLp_mul_weight {g : E → ℂ} (hg : g.HasTemperateGrowth) {t K : ℝ} {j : ℕ}
    (hj : (Module.finrank ℝ E : ℝ) < 2 * j + 2 * t)
    (hbound : ∀ ξ, ‖g ξ‖ ≤ K * (1 + ‖ξ‖ ^ 2) ^ (-(j : ℝ) / 2)) :
    MemLp (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume := by
  have hint := (integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := 2 * j + 2 * t) hj).const_mul (K ^ 2)
  have hmeas : AEStronglyMeasurable (fun ξ ↦ g ξ * weight (-t) ξ) volume :=
    (hg.1.continuous.mul (weight_hasTemperateGrowth (E := E) (-t)).1.continuous).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hint.mono' (hmeas.norm.pow 2) (ae_of_all _ fun ξ ↦ ?_)
  have hp : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_weight, mul_pow]
  calc ‖g ξ‖ ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ (-t / 2)) ^ 2
      ≤ (K * (1 + ‖ξ‖ ^ 2) ^ (-(j : ℝ) / 2)) ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ (-t / 2)) ^ 2 := by
        gcongr; exact hbound ξ
    _ = K ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * j + 2 * t) / 2) := by
        rw [mul_pow, mul_assoc, ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-(j : ℝ) / 2)) 2,
          ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-t / 2)) 2, ← Real.rpow_mul hp.le,
          ← Real.rpow_mul hp.le, ← Real.rpow_add hp]
        congr 2; push_cast; ring

theorem IsEllipticAt.exists_local_solution [Nontrivial E] {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ}
    {x₀ : E} (hT : IsEllipticAt T m x₀) (hm : 1 ≤ m) {t : ℝ}
    (ht : t < -(Module.finrank ℝ E : ℝ) / 2) :
    ∃ r > 0, ∃ E₀ : 𝓢'(E, ℂ), MemSobolev (t + m) 2 E₀ ∧
      Distribution.IsVanishingOn (T E₀ - TemperedDistribution.delta x₀) (Metric.ball x₀ r) := by
  obtain ⟨n, a, w, N, rfl, hN, hNl, cl, Cu, hcl, hCu, hlow, hup⟩ := hT.exists_data hm
  set k : ℕ := ⌈(Module.finrank ℝ E : ℝ) - 2 * t⌉₊ + 1
  have hk : (Module.finrank ℝ E : ℝ) < 2 * ((2 * m * k : ℕ) : ℝ) + 2 * t := by
    have h1 : (Module.finrank ℝ E : ℝ) - 2 * t < k := by
      have := Nat.le_ceil ((Module.finrank ℝ E : ℝ) - 2 * t)
      simp only [k]; push_cast; linarith
    have h2 : (k : ℝ) ≤ ((2 * m * k : ℕ) : ℝ) := by
      have : k ≤ 2 * m * k := by nlinarith
      exact_mod_cast this
    linarith
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_small a w N x₀ hcl hCu hlow hup hm hN k
  obtain ⟨μ, hμ0, hμ1, hb⟩ := hsmall {t}
  have hK' := (hb t (by simp)).2
  set g := rNSymb (fun i ↦ a i x₀) w μ k
  have hg : g.HasTemperateGrowth := rNSymb_hasTemperateGrowth _ w μ k
  have hA := memLp_weight (E := E) ht
  have hB : MemLp (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume :=
    memLp_mul_weight hg hk (rNSymb_bound _ w hcl hCu hlow hup hμ0 k)
  obtain ⟨r, hr, hrδ, hrsmall⟩ := exists_bump_small x₀
    (C := (eLpNorm (weight t : E → ℂ) 2 volume).toReal *
      (eLpNorm (fun ξ ↦ g ξ * weight (-t) ξ) 2 volume).toReal) (by positivity) hδ₀
  have hχR : OpBound (smulLeftCLM ℂ (bump x₀ hr : E → ℂ) ∘L Rop a w x₀ μ k) t t (1 / 4) :=
    (opBound_smulLeft_fourierMultiplier (bump x₀ hr) hg t hA hB).mono (by rw [mul_assoc]; exact hrsmall)
  have hK'' := hK'.sub hχR (by norm_num) (by norm_num)
  obtain ⟨v, hv, hvK⟩ := exists_add_eq_of_opBound_lt (by norm_num) (by norm_num) hK''
    (memSobolev_delta x₀ ht)
  refine ⟨r, hr, Qop a w x₀ μ k v, ?_, ?_⟩
  · exact (opBound_Qop a w x₀ hcl hCu hlow hup hμ0.le hμ1 k (t + m)).memSobolev
      (by convert hv using 2; ring)
  · have hZ := isVanishingOn_prinOp_add_sub a w N x₀ hδ₀ (Qop a w x₀ μ k v)
    have hP : P0 a w x₀ (Qop a w x₀ μ k v) = v - Rop a w x₀ μ k v := by
      have := congrArg (fun A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) ↦ A v) (frozenOperator_comp_parametrix a w x₀ hμ0.le k)
      simpa using this
    have hcut : Distribution.IsVanishingOn
        (smulLeftCLM ℂ (bump x₀ hr : E → ℂ) (Rop a w x₀ μ k v) - Rop a w x₀ μ k v)
        (Metric.ball x₀ r) :=
      isVanishingOn_smulLeftCLM_sub (bump x₀ hr).hasTemperateGrowth
        (fun x hx ↦ bump_eq_one x₀ hr (Metric.ball_subset_closedBall hx)) _
    have e : (prinOp a w + N) (Qop a w x₀ μ k v) - TemperedDistribution.delta x₀ =
        ((prinOp a w + N) (Qop a w x₀ μ k v) -
          (P0 a w x₀ (Qop a w x₀ μ k v) + locM a w N x₀ hδ₀ (Qop a w x₀ μ k v))) +
        (smulLeftCLM ℂ (bump x₀ hr : E → ℂ) (Rop a w x₀ μ k v) - Rop a w x₀ μ k v) := by
      rw [← hvK, hP]
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      abel
    rw [e]
    exact isVanishingOn_add (hZ.mono (Metric.ball_subset_ball hrδ)) hcut

end

end GroundTheory.Automorphic.Sobolev
