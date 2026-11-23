import Mathlib

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem toTemperedDistribution_injective :
    Function.Injective (fun f : Lp F 2 (volume : Measure E) ↦ (f : 𝓢'(E, F))) := by
  intro f g h
  have := (LinearMap.ker_eq_bot (f := (Lp.toTemperedDistributionCLM F (volume : Measure E) 2 :
    Lp F 2 (volume : Measure E) →ₗ[ℂ] 𝓢'(E, F)))).1
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F) (μ := (volume : Measure E)))
  exact this h

variable (E F) in

def sobolevSubmodule (s : ℝ) : Submodule ℂ 𝓢'(E, F) where
  carrier := {u | MemSobolev s 2 u}
  add_mem' hu hv := hu.add hv
  zero_mem' := memSobolev_fun_zero E F s 2
  smul_mem' c _ hu := hu.smul c

def sobolevToLp {s : ℝ} (u : sobolevSubmodule E F s) : Lp F 2 (volume : Measure E) :=
  Classical.choose u.2

theorem besselPotential_eq_sobolevToLp {s : ℝ} (u : sobolevSubmodule E F s) :
    besselPotential E F s (u : 𝓢'(E, F)) = (sobolevToLp u : 𝓢'(E, F)) :=
  Classical.choose_spec u.2

theorem sobolevToLp_eq_iff {s : ℝ} (u : sobolevSubmodule E F s) (f : Lp F 2 (volume : Measure E)) :
    sobolevToLp u = f ↔ besselPotential E F s (u : 𝓢'(E, F)) = (f : 𝓢'(E, F)) := by
  constructor
  · rintro rfl; exact besselPotential_eq_sobolevToLp u
  · intro h; exact toTemperedDistribution_injective ((besselPotential_eq_sobolevToLp u).symm.trans h)

theorem memSobolev_besselPotential_neg (s : ℝ) (f : Lp F 2 (volume : Measure E)) :
    MemSobolev s 2 (besselPotential E F (-s) (f : 𝓢'(E, F))) :=
  ⟨f, by simp⟩

variable (E F) in

def sobolevEquivLp (s : ℝ) : sobolevSubmodule E F s ≃ₗ[ℂ] Lp F 2 (volume : Measure E) where
  toFun := sobolevToLp
  map_add' u v := by
    rw [sobolevToLp_eq_iff, Submodule.coe_add, map_add, besselPotential_eq_sobolevToLp, besselPotential_eq_sobolevToLp,
      ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply,
      ← Lp.toTemperedDistributionCLM_apply, map_add]
  map_smul' c u := by
    rw [sobolevToLp_eq_iff, Submodule.coe_smul, map_smul, besselPotential_eq_sobolevToLp,
      ← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_smul,
      RingHom.id_apply]
  invFun f := ⟨besselPotential E F (-s) (f : 𝓢'(E, F)), memSobolev_besselPotential_neg s f⟩
  left_inv u := by
    apply Subtype.ext
    simp only
    rw [← besselPotential_eq_sobolevToLp, besselPotential_besselPotential_apply]
    simp
  right_inv f := by
    rw [sobolevToLp_eq_iff]
    simp

theorem sobolevEquivLp_apply {s : ℝ} (u : sobolevSubmodule E F s) :
    (sobolevEquivLp E F s u : 𝓢'(E, F)) = besselPotential E F s (u : 𝓢'(E, F)) :=
  (besselPotential_eq_sobolevToLp u).symm

variable (E F) in

def SobolevSpace (s : ℝ) : Type _ := sobolevSubmodule E F s

namespace SobolevSpace

variable {s : ℝ}

instance : AddCommGroup (SobolevSpace E F s) :=
  inferInstanceAs (AddCommGroup (sobolevSubmodule E F s))

instance : Module ℂ (SobolevSpace E F s) :=
  inferInstanceAs (Module ℂ (sobolevSubmodule E F s))

def bessel (s : ℝ) : SobolevSpace E F s ≃ₗ[ℂ] Lp F 2 (volume : Measure E) :=
  sobolevEquivLp E F s

instance : NormedAddCommGroup (SobolevSpace E F s) :=
  NormedAddCommGroup.induced _ _ (bessel (E := E) (F := F) s) (bessel s).injective

instance : InnerProductSpace ℂ (SobolevSpace E F s) :=
  InnerProductSpace.induced (bessel (E := E) (F := F) s)

def toDistribution (u : SobolevSpace E F s) : 𝓢'(E, F) := Subtype.val (show sobolevSubmodule E F s from u)

theorem norm_def (u : SobolevSpace E F s) : ‖u‖ = ‖bessel s u‖ := rfl

theorem inner_def (u v : SobolevSpace E F s) :
    inner ℂ u v = inner ℂ (bessel s u) (bessel s v) := rfl

end SobolevSpace

namespace SobolevSpace

variable {s : ℝ}

def besselₗᵢ (s : ℝ) : SobolevSpace E F s ≃ₗᵢ[ℂ] Lp F 2 (volume : Measure E) where
  toLinearEquiv := bessel s
  norm_map' _ := rfl

theorem besselₗᵢ_apply (u : SobolevSpace E F s) : besselₗᵢ s u = bessel s u := rfl

theorem toDistribution_bessel (u : SobolevSpace E F s) :
    (bessel s u : 𝓢'(E, F)) = besselPotential E F s (toDistribution u) :=
  sobolevEquivLp_apply _

theorem toDistribution_bessel_symm (f : Lp F 2 (volume : Measure E)) :
    toDistribution ((bessel (E := E) (F := F) s).symm f) = besselPotential E F (-s) (f : 𝓢'(E, F)) :=
  rfl

theorem toDistribution_eq_besselPotential (u : SobolevSpace E F s) :
    toDistribution u = besselPotential E F (-s) (bessel s u : 𝓢'(E, F)) := by
  rw [← toDistribution_bessel_symm, LinearEquiv.symm_apply_apply]

instance : CompleteSpace (SobolevSpace E F s) :=
  (completeSpace_congr (e := (besselₗᵢ (E := E) (F := F) s).toEquiv)
    (besselₗᵢ s).isometry.isUniformEmbedding).2 inferInstance

theorem toDistribution_injective :
    Function.Injective (toDistribution : SobolevSpace E F s → 𝓢'(E, F)) :=
  fun _ _ h ↦ Subtype.ext h

@[simp] theorem toDistribution_add (u v : SobolevSpace E F s) :
    toDistribution (u + v) = toDistribution u + toDistribution v := rfl

@[simp] theorem toDistribution_smul (c : ℂ) (u : SobolevSpace E F s) :
    toDistribution (c • u) = c • toDistribution u := rfl

@[simp] theorem toDistribution_zero : toDistribution (0 : SobolevSpace E F s) = 0 := rfl

theorem memSobolev_toDistribution (u : SobolevSpace E F s) : MemSobolev s 2 (toDistribution u) :=
  (show sobolevSubmodule E F s from u).2

def mk (u : 𝓢'(E, F)) (hu : MemSobolev s 2 u) : SobolevSpace E F s :=
  (⟨u, hu⟩ : sobolevSubmodule E F s)

@[simp] theorem toDistribution_mk (u : 𝓢'(E, F)) (hu : MemSobolev s 2 u) :
    toDistribution (mk u hu) = u := rfl

theorem exists_toDistribution_eq_iff (u : 𝓢'(E, F)) :
    (∃ v : SobolevSpace E F s, toDistribution v = u) ↔ MemSobolev s 2 u :=
  ⟨fun ⟨v, hv⟩ ↦ hv ▸ memSobolev_toDistribution v, fun hu ↦ ⟨mk u hu, rfl⟩⟩

variable (E F s) in

def toDistributionCLM : SobolevSpace E F s →L[ℂ] 𝓢'(E, F) :=
  besselPotential E F (-s) ∘L Lp.toTemperedDistributionCLM F (volume : Measure E) 2 ∘L
    (besselₗᵢ (E := E) (F := F) s).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem toDistributionCLM_apply (u : SobolevSpace E F s) :
    toDistributionCLM E F s u = toDistribution u := by
  rw [toDistribution_eq_besselPotential]
  rfl

end SobolevSpace

section Multiplication

variable {m : E → ℂ} {C : ℝ}

theorem memLp_smul_of_bounded (hm : m.HasTemperateGrowth) (hC : ∀ x, ‖m x‖ ≤ C)
    (h : Lp F 2 (volume : Measure E)) : MemLp (fun x ↦ m x • h x) 2 (volume : Measure E) :=
  (Lp.memLp h).of_le_mul (c := C)
    (hm.1.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable h))
    (ae_of_all _ fun x ↦ by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

def boundedMulLp (hm : m.HasTemperateGrowth) (hC : ∀ x, ‖m x‖ ≤ C) (h : Lp F 2 (volume : Measure E)) :
    Lp F 2 (volume : Measure E) :=
  (memLp_smul_of_bounded hm hC h).toLp _

theorem coeFn_boundedMulLp (hm : m.HasTemperateGrowth) (hC : ∀ x, ‖m x‖ ≤ C)
    (h : Lp F 2 (volume : Measure E)) : boundedMulLp hm hC h =ᵐ[volume] fun x ↦ m x • h x :=
  (memLp_smul_of_bounded hm hC h).coeFn_toLp

theorem toTemperedDistribution_boundedMulLp (hm : m.HasTemperateGrowth) (hC : ∀ x, ‖m x‖ ≤ C)
    (h : Lp F 2 (volume : Measure E)) :
    (boundedMulLp hm hC h : 𝓢'(E, F)) = smulLeftCLM F m (h : 𝓢'(E, F)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hm]
  apply integral_congr_ae
  filter_upwards [coeFn_boundedMulLp hm hC h] with x hx
  rw [hx, smul_smul, mul_comm, smul_eq_mul]

theorem norm_boundedMulLp_le (hm : m.HasTemperateGrowth) (hC : ∀ x, ‖m x‖ ≤ C)
    (h : Lp F 2 (volume : Measure E)) : ‖boundedMulLp hm hC h‖ ≤ C * ‖h‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_boundedMulLp hm hC h] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem fourierMultiplierCLM_toTemperedDistribution (hm : m.HasTemperateGrowth)
    (hC : ∀ x, ‖m x‖ ≤ C) (f : Lp F 2 (volume : Measure E)) :
    fourierMultiplierCLM F m (f : 𝓢'(E, F)) =
      ((𝓕⁻ (boundedMulLp hm hC (𝓕 f)) : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  rw [fourierMultiplierCLM_apply, Lp.fourier_toTemperedDistribution_eq,
    ← toTemperedDistribution_boundedMulLp hm hC, Lp.fourierInv_toTemperedDistribution_eq]

theorem norm_fourierInv_boundedMulLp_le (hm : m.HasTemperateGrowth) (hC : ∀ x, ‖m x‖ ≤ C)
    (f : Lp F 2 (volume : Measure E)) :
    ‖(𝓕⁻ (boundedMulLp hm hC (𝓕 f)) : Lp F 2 (volume : Measure E))‖ ≤ C * ‖f‖ := by
  have h1 : ‖(𝓕⁻ (boundedMulLp hm hC (𝓕 f)) : Lp F 2 (volume : Measure E))‖ = ‖boundedMulLp hm hC (𝓕 f)‖ :=
    (Lp.fourierTransformₗᵢ E F).symm.norm_map _
  rw [h1]
  calc _ ≤ C * ‖𝓕 f‖ := norm_boundedMulLp_le hm hC _
    _ = C * ‖f‖ := by rw [Lp.norm_fourier_eq]

end Multiplication

def weight (r : ℝ) (ξ : E) : ℂ := (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)

theorem weight_hasTemperateGrowth (r : ℝ) : (weight r : E → ℂ).HasTemperateGrowth := by
  unfold weight; fun_prop

theorem besselPotential_eq_fourierMultiplierCLM (r : ℝ) :
    besselPotential E F r = fourierMultiplierCLM F (weight r) := rfl

theorem weight_mul_weight (r r' : ℝ) (ξ : E) : weight r ξ * weight r' ξ = weight (r + r') ξ := by
  unfold weight
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  congr 2; ring

theorem norm_weight (r : ℝ) (ξ : E) : ‖weight r ξ‖ = (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  unfold weight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem weight_pos (r : ℝ) (ξ : E) : 0 < (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by positivity

variable {m : E → ℂ} {C s t : ℝ}

theorem bound_nonneg (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) : 0 ≤ C := by
  have h := hC 0
  have hp : 0 < (1 + ‖(0 : E)‖ ^ 2) ^ ((s - t) / 2) := by positivity
  by_contra hneg
  push Not at hneg
  have : C * (1 + ‖(0 : E)‖ ^ 2) ^ ((s - t) / 2) < 0 := mul_neg_of_neg_of_pos hneg hp
  linarith [norm_nonneg (m 0)]

theorem bounded_mul_weight (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (ξ : E) :
    ‖m ξ * weight (t - s) ξ‖ ≤ C := by
  rw [norm_mul, norm_weight]
  have h1 := hC ξ
  have hp := weight_pos (t - s) ξ
  calc ‖m ξ‖ * (1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2)
      ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((t - s) / 2) :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ = C := by
        rw [mul_assoc, ← Real.rpow_add (by positivity),
          show (s - t) / 2 + (t - s) / 2 = 0 by ring, Real.rpow_zero, mul_one]

theorem hasTemperateGrowth_mul_weight (hm : m.HasTemperateGrowth) (r : ℝ) :
    (fun ξ ↦ m ξ * weight r ξ).HasTemperateGrowth :=
  hm.mul (weight_hasTemperateGrowth _)

namespace SobolevSpace

theorem besselPotential_fourierMultiplier (hm : m.HasTemperateGrowth) (u : SobolevSpace E F s) :
    besselPotential E F t (fourierMultiplierCLM F m (toDistribution u)) =
      fourierMultiplierCLM F (fun ξ ↦ m ξ * weight (t - s) ξ) (bessel s u : 𝓢'(E, F)) := by
  rw [toDistribution_eq_besselPotential, besselPotential_eq_fourierMultiplierCLM,
    besselPotential_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (weight_hasTemperateGrowth _) hm,
    fourierMultiplierCLM_fourierMultiplierCLM_apply
      ((weight_hasTemperateGrowth _).mul hm) (weight_hasTemperateGrowth _)]
  have key : (weight (-s) * m * weight t : E → ℂ) = fun ξ ↦ m ξ * weight (t - s) ξ := by
    funext ξ
    simp only [Pi.mul_apply]
    rw [mul_comm (weight (-s) ξ) (m ξ), mul_assoc, weight_mul_weight]
    congr 2; ring
  rw [key]

theorem memSobolev_fourierMultiplier (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    MemSobolev t 2 (fourierMultiplierCLM F m (toDistribution u)) :=
  ⟨_, by
    rw [besselPotential_fourierMultiplier hm u,
      fourierMultiplierCLM_toTemperedDistribution (hasTemperateGrowth_mul_weight hm (t - s))
        (bounded_mul_weight hC)]⟩

def multiplierₗ (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) :
    SobolevSpace E F s →ₗ[ℂ] SobolevSpace E F t where
  toFun u := mk _ (memSobolev_fourierMultiplier hm hC u)
  map_add' u v := toDistribution_injective (by simp)
  map_smul' c u := toDistribution_injective (by simp)

theorem bessel_multiplierₗ (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    bessel t (multiplierₗ hm hC u) =
      𝓕⁻ (boundedMulLp (hasTemperateGrowth_mul_weight hm (t - s)) (bounded_mul_weight hC)
        (𝓕 (bessel s u))) := by
  apply toTemperedDistribution_injective
  simp only
  rw [toDistribution_bessel, ← fourierMultiplierCLM_toTemperedDistribution]
  exact besselPotential_fourierMultiplier hm u

def multiplier (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) :
    SobolevSpace E F s →L[ℂ] SobolevSpace E F t :=
  (multiplierₗ hm hC).mkContinuous C fun u ↦ by
    rw [norm_def, norm_def, bessel_multiplierₗ]
    exact norm_fourierInv_boundedMulLp_le _ _ _

@[simp] theorem toDistribution_multiplier (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    toDistribution (multiplier hm hC u) = fourierMultiplierCLM F m (toDistribution u) := rfl

theorem norm_multiplier_le (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) :
    ‖multiplier (E := E) (F := F) hm hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (bound_nonneg hC) _

theorem norm_multiplier_apply_le (hm : m.HasTemperateGrowth)
    (hC : ∀ ξ, ‖m ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) (u : SobolevSpace E F s) :
    ‖multiplier hm hC u‖ ≤ C * ‖u‖ :=
  ((multiplier hm hC).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_multiplier_le hm hC) (norm_nonneg _))

end SobolevSpace

theorem Lp_two_norm_sq_eq_integral (f : Lp F 2 (volume : Measure E)) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  simp_rw [inner_self_eq_norm_sq]

def fourierFun {s : ℝ} (u : SobolevSpace E F s) (ξ : E) : F :=
  weight (-s) ξ • (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) ξ

theorem smulLeftCLM_weight_fourier {s : ℝ} (u : SobolevSpace E F s) :
    smulLeftCLM F (weight s) (𝓕 (SobolevSpace.toDistribution u)) =
      ((𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  rw [← Lp.fourier_toTemperedDistribution_eq, SobolevSpace.toDistribution_bessel,
    besselPotential_eq_fourierMultiplierCLM, fourierMultiplierCLM_apply, fourier_fourierInv_eq]

theorem integral_smul_weight (r : ℝ) (φ : 𝓢(E, ℂ)) (g : Lp F 2 (volume : Measure E)) :
    (g : 𝓢'(E, F)) (SchwartzMap.smulLeftCLM ℂ (weight r) φ) =
      ∫ ξ, φ ξ • (weight r ξ • g ξ) := by
  rw [Lp.toTemperedDistribution_apply]
  congr 1; ext ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth r)]
  simp only [smul_smul, smul_eq_mul, mul_comm]

theorem fourier_apply_eq_integral {s : ℝ} (u : SobolevSpace E F s) (φ : 𝓢(E, ℂ)) :
    𝓕 (SobolevSpace.toDistribution u) φ = ∫ ξ, φ ξ • fourierFun u ξ := by
  have h1 : 𝓕 (SobolevSpace.toDistribution u) =
      smulLeftCLM F (weight (-s)) (smulLeftCLM F (weight s) (𝓕 (SobolevSpace.toDistribution u))) := by
    rw [smulLeftCLM_smulLeftCLM_apply (weight_hasTemperateGrowth _) (weight_hasTemperateGrowth _)]
    have : (weight s * weight (-s) : E → ℂ) = fun _ ↦ 1 := by
      funext ξ; simp only [Pi.mul_apply]; rw [weight_mul_weight]; simp [weight]
    rw [this, smulLeftCLM_const, one_smul]
  rw [h1, smulLeftCLM_weight_fourier, smulLeftCLM_apply_apply, integral_smul_weight]
  rfl

theorem fourierFun_aestronglyMeasurable {s : ℝ} (u : SobolevSpace E F s) :
    AEStronglyMeasurable (fourierFun u) (volume : Measure E) :=
  (weight_hasTemperateGrowth (-s)).1.continuous.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable _)

theorem weight_smul_fourierFun {s : ℝ} (u : SobolevSpace E F s) (ξ : E) :
    weight s ξ • fourierFun u ξ = (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) ξ := by
  rw [fourierFun, smul_smul, weight_mul_weight]; simp [weight]

theorem norm_sq_eq_integral {s : ℝ} (u : SobolevSpace E F s) :
    ‖u‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun u ξ‖ ^ 2 := by
  rw [SobolevSpace.norm_def, ← Lp.norm_fourier_eq, Lp_two_norm_sq_eq_integral]
  congr 1; ext ξ
  rw [← weight_smul_fourierFun, norm_smul, norm_weight, mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

theorem memSobolev_iff_fourier {s : ℝ} (u : 𝓢'(E, F)) :
    MemSobolev s 2 u ↔ ∃ g : E → F, MemLp (fun ξ ↦ weight s ξ • g ξ) 2 (volume : Measure E) ∧
      ∀ φ : 𝓢(E, ℂ), 𝓕 u φ = ∫ ξ, φ ξ • g ξ := by
  constructor
  · intro hu
    set v : SobolevSpace E F s := SobolevSpace.mk u hu
    refine ⟨fourierFun v, ?_, fourier_apply_eq_integral v⟩
    have : (fun ξ ↦ weight s ξ • fourierFun v ξ) =
        ⇑(𝓕 (SobolevSpace.bessel s v) : Lp F 2 (volume : Measure E)) := by
      funext ξ; exact weight_smul_fourierFun v ξ
    rw [this]; exact Lp.memLp _
  · rintro ⟨g, hg, hφ⟩
    rw [memSobolev_iff_exists_smulLeftCLM_fourier]
    refine ⟨hg.toLp _, ?_⟩
    ext φ
    rw [smulLeftCLM_apply_apply, hφ, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with ξ hξ
    erw [SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth s)]
    rw [hξ]
    simp only [smul_smul, smul_eq_mul, mul_comm]

theorem norm_sq_eq_integral_of_fourier {s : ℝ} (u : SobolevSpace E F s) (g : E → F)
    (hg : MemLp (fun ξ ↦ weight s ξ • g ξ) 2 (volume : Measure E))
    (hφ : ∀ φ : 𝓢(E, ℂ), 𝓕 (SobolevSpace.toDistribution u) φ = ∫ ξ, φ ξ • g ξ) :
    g =ᵐ[volume] fourierFun u ∧ ‖u‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖g ξ‖ ^ 2 := by
  have hL : hg.toLp _ = (𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) := by
    apply toTemperedDistribution_injective
    simp only
    rw [← smulLeftCLM_weight_fourier]
    ext φ
    rw [smulLeftCLM_apply_apply, hφ, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with ξ hξ
    rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (weight_hasTemperateGrowth s)]
    simp only [smul_smul, smul_eq_mul, mul_comm]
  have hae : (fun ξ ↦ weight s ξ • g ξ) =ᵐ[volume] fun ξ ↦ weight s ξ • fourierFun u ξ := by
    have h2 : ⇑(hg.toLp _) =ᵐ[volume] ⇑(𝓕 (SobolevSpace.bessel s u) :
        Lp F 2 (volume : Measure E)) := by rw [hL]
    filter_upwards [hg.coeFn_toLp, h2] with ξ h1 h2
    rw [← h1, h2, weight_smul_fourierFun]
  have hg' : g =ᵐ[volume] fourierFun u := by
    filter_upwards [hae] with ξ h
    have hw : weight s ξ ≠ 0 := by
      unfold weight; exact_mod_cast (weight_pos s ξ).ne'
    exact smul_right_injective F hw h
  refine ⟨hg', ?_⟩
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [hg'] with ξ h
  rw [h]

theorem ae_eq_of_integral_schwartz_smul_eq {g₁ g₂ : E → F}
    (h₁ : LocallyIntegrable g₁ (volume : Measure E)) (h₂ : LocallyIntegrable g₂ (volume : Measure E))
    (h : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → ∫ x, φ x • g₁ x = ∫ x, φ x • g₂ x) :
    g₁ =ᵐ[volume] g₂ := by
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero (h₁.sub h₂) fun g g_smooth g_cpt ↦ by
    have hc₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hc₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    set φ := hc₁.toSchwartzMap hc₂
    have hφ : ∀ x, φ x = (g x : ℂ) := fun x ↦ rfl
    have hφc : HasCompactSupport φ := hc₁
    have i₁ : Integrable (fun x ↦ φ x • g₁ x) (volume : Measure E) :=
      h₁.integrable_smul_left_of_hasCompactSupport φ.continuous hφc
    have i₂ : Integrable (fun x ↦ φ x • g₂ x) (volume : Measure E) :=
      h₂.integrable_smul_left_of_hasCompactSupport φ.continuous hφc
    have e : ∀ x, g x • (g₁ - g₂) x = φ x • g₁ x - φ x • g₂ x := fun x ↦ by
      rw [hφ, Pi.sub_apply, smul_sub, Complex.coe_smul, Complex.coe_smul]
    simp_rw [e]
    rw [integral_sub i₁ i₂, h φ hφc, sub_self]
  filter_upwards [this] with x hx
  exact sub_eq_zero.1 hx

theorem integral_fourier_smul_eq_of_integrable (φ : 𝓢(E, ℂ)) {g : E → F}
    (hg : Integrable g (volume : Measure E)) :
    ∫ ξ, 𝓕 φ ξ • g ξ = ∫ x, φ x • 𝓕 g x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E)
    Real.continuous_fourierChar continuous_inner φ.integrable hg

namespace SobolevSpace

def lpEquivSobolevZero : Lp F 2 (volume : Measure E) ≃ₗᵢ[ℂ] SobolevSpace E F 0 :=
  (besselₗᵢ 0).symm

@[simp] theorem toDistribution_l2Equiv (f : Lp F 2 (volume : Measure E)) :
    toDistribution (lpEquivSobolevZero f) = (f : 𝓢'(E, F)) := by
  change toDistribution ((bessel 0).symm f) = _
  rw [toDistribution_bessel_symm, neg_zero, besselPotential_zero]
  rfl

variable {s t : ℝ}

theorem one_bound (h : t ≤ s) (ξ : E) :
    ‖(1 : ℂ)‖ ≤ 1 * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2) := by
  rw [norm_one, one_mul]
  exact Real.one_le_rpow (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)

def inclusion (h : t ≤ s) : SobolevSpace E F s →L[ℂ] SobolevSpace E F t :=
  multiplier (m := fun _ ↦ (1 : ℂ)) (Function.HasTemperateGrowth.const 1) (one_bound h)

@[simp] theorem toDistribution_inclusion (h : t ≤ s) (u : SobolevSpace E F s) :
    toDistribution (inclusion h u) = toDistribution u := by
  rw [inclusion, toDistribution_multiplier, fourierMultiplierCLM_const]
  simp

theorem norm_inclusion_apply_le (h : t ≤ s) (u : SobolevSpace E F s) :
    ‖inclusion h u‖ ≤ ‖u‖ := by
  have := norm_multiplier_apply_le (m := fun _ ↦ (1 : ℂ)) (F := F)
    (Function.HasTemperateGrowth.const 1) (one_bound h) u
  rw [one_mul] at this
  exact this

end SobolevSpace

namespace SobolevSpace

variable {s : ℝ}

def ofSchwartz (s : ℝ) (φ : 𝓢(E, F)) : SobolevSpace E F s :=
  mk (φ : 𝓢'(E, F)) φ.memSobolev

@[simp] theorem toDistribution_ofSchwartz (φ : 𝓢(E, F)) :
    toDistribution (ofSchwartz s φ) = (φ : 𝓢'(E, F)) := rfl

theorem besselₗᵢ_symm_toLp (ψ : 𝓢(E, F)) :
    (besselₗᵢ s).symm (ψ.toLp 2) =
      ofSchwartz s (SchwartzMap.fourierMultiplierCLM F (weight (-s)) ψ) := by
  rw [LinearIsometryEquiv.symm_apply_eq, besselₗᵢ_apply]
  apply toTemperedDistribution_injective
  simp only
  rw [toDistribution_bessel, toDistribution_ofSchwartz, Lp.toTemperedDistribution_toLp_eq,
    ← fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth _),
    ← besselPotential_eq_fourierMultiplierCLM, besselPotential_besselPotential_apply]
  simp

theorem denseRange_ofSchwartz : DenseRange (ofSchwartz (E := E) (F := F) s) := by
  have h : DenseRange (fun ψ : 𝓢(E, F) ↦ (besselₗᵢ (E := E) (F := F) s).symm (ψ.toLp 2)) :=
    (besselₗᵢ s).symm.toHomeomorph.surjective.denseRange.comp
      (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top)
      (besselₗᵢ s).symm.continuous
  refine Dense.mono ?_ h
  rintro _ ⟨ψ, rfl⟩
  exact ⟨_, (besselₗᵢ_symm_toLp ψ).symm⟩

open LineDeriv in
theorem lineDeriv_bound (v : E) (ξ : E) :
    ‖(2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ)‖ ≤
      (2 * Real.pi * ‖v‖) * (1 + ‖ξ‖ ^ 2) ^ ((s - (s - 1)) / 2) := by
  rw [show (s - (s - 1)) / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have h2 : ‖(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Complex.norm_two,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2]
  have h : |inner ℝ ξ v| ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2) :=
    calc |inner ℝ ξ v| ≤ ‖ξ‖ * ‖v‖ := abs_real_inner_le_norm ξ v
      _ = ‖v‖ * ‖ξ‖ := mul_comm _ _
      _ ≤ ‖v‖ * √(1 + ‖ξ‖ ^ 2) := by
          gcongr
          exact Real.le_sqrt_of_sq_le (by linarith)
  calc 2 * Real.pi * |inner ℝ ξ v| ≤ 2 * Real.pi * (‖v‖ * √(1 + ‖ξ‖ ^ 2)) := by
        gcongr
    _ = _ := by ring

open LineDeriv in

def lineDerivCLM (v : E) : SobolevSpace E F s →L[ℂ] SobolevSpace E F (s - 1) :=
  multiplier (m := fun ξ ↦ (2 * Real.pi * Complex.I) * ((inner ℝ ξ v : ℝ) : ℂ))
    (by fun_prop) (lineDeriv_bound v)

open LineDeriv in
@[simp] theorem toDistribution_lineDerivCLM (v : E) (u : SobolevSpace E F s) :
    toDistribution (lineDerivCLM v u) = ∂_{v} (toDistribution u) := by
  rw [lineDerivCLM, toDistribution_multiplier, lineDeriv_eq_fourierMultiplierCLM]
  have h := fourierMultiplierCLM_smul (F := F) (g := fun x : E ↦ ((inner ℝ x v : ℝ) : ℂ))
    (by fun_prop) (2 * Real.pi * Complex.I)
  rw [← smul_apply, ← h]
  rfl

theorem norm_lineDerivCLM_apply_le (v : E) (u : SobolevSpace E F s) :
    ‖lineDerivCLM v u‖ ≤ 2 * Real.pi * ‖v‖ * ‖u‖ :=
  norm_multiplier_apply_le _ _ u

end SobolevSpace

end

end GroundTheory.Automorphic.Sobolev
