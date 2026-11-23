import Mathlib

open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real

noncomputable section

namespace GlobalTheory

local notation "𝕢" => Function.Periodic.qParam

def HasQExpansion (h : ℝ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m ↦ coeff m φ * 𝕢 h τ ^ m) (f τ)

namespace HasQExpansion

variable {h : ℝ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}

lemma one_le_radius (hh : 0 < h) (hf : HasQExpansion h f φ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ coeff m φ)).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  rcases eq_or_ne r 0 with rfl | hr'
  · simp
  · lift r to NNReal using hr.ne_top
    apply FormalMultilinearSeries.le_radius_of_summable
    have hq : ‖((r : ℝ) : ℂ)‖ < 1 := by simpa using hr
    have hq1 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr'
    have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
    have := (hf ⟨_, h1⟩).summable.norm
    simp only [Periodic.qParam_right_inv hh.ne' hq1] at this
    simpa [norm_mul] using this

lemma exists_analytic (hh : 0 < h) (hf : HasQExpansion h f φ) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 1) ∧ F 0 = coeff 0 φ ∧
      ∀ τ : ℍ, f τ = F (𝕢 h τ) := by
  set p := FormalMultilinearSeries.ofScalars ℂ (fun m ↦ coeff m φ) with hp
  have h1 : 1 ≤ p.radius := hf.one_le_radius hh
  have h2 : HasFPowerSeriesOnBall p.sum p 0 1 :=
    (p.hasFPowerSeriesOnBall (zero_lt_one.trans_le h1)).mono zero_lt_one h1
  refine ⟨p.sum, ?_, ?_, fun τ ↦ ?_⟩
  · have := h2.analyticOnNhd
    rwa [← ENNReal.coe_one, Metric.eball_coe] at this
  · rw [← h2.coeff_zero (fun _ ↦ 0)]
    simp [hp, FormalMultilinearSeries.ofScalars_apply_eq']
  · rw [FormalMultilinearSeries.sum, ← (hf τ).tsum_eq]
    simp [hp, FormalMultilinearSeries.ofScalars_apply_eq', mul_comm]

lemma tendsto (hh : 0 < h) (hf : HasQExpansion h f φ) :
    Tendsto f atImInfty (𝓝 (coeff 0 φ)) := by
  obtain ⟨F, hF, h0, hfF⟩ := hf.exists_analytic hh
  rw [show f = F ∘ fun τ : ℍ ↦ 𝕢 h τ from funext hfF, ← h0]
  exact (hF 0 (by simp)).continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)

lemma isBoundedAtImInfty (hh : 0 < h) (hf : HasQExpansion h f φ) : IsBoundedAtImInfty f :=
  (hf.tendsto hh).isBigO_one ℝ

lemma mdifferentiable (hh : 0 < h) (hf : HasQExpansion h f φ) : MDiff f := by
  obtain ⟨F, hF, -, hfF⟩ := hf.exists_analytic hh
  rw [UpperHalfPlane.mdifferentiable_iff]
  have : DifferentiableOn ℂ (fun z ↦ F (𝕢 h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have h1 : DifferentiableAt ℂ F (𝕢 h z) :=
      (hF _ (by simpa using Periodic.norm_qParam_lt_one hh hz)).differentiableAt
    exact (h1.comp z (Periodic.differentiable_qParam z)).differentiableWithinAt
  refine this.congr fun z hz ↦ ?_
  simp [ofComplex_apply_of_im_pos hz, hfF]

lemma congr (hf : HasQExpansion h f φ) (hfg : ∀ τ, g τ = f τ) : HasQExpansion h g φ :=
  fun τ ↦ hfg τ ▸ hf τ

lemma add (hf : HasQExpansion h f φ) (hg : HasQExpansion h g ψ) :
    HasQExpansion h (fun τ ↦ f τ + g τ) (φ + ψ) := fun τ ↦ by
  simpa [add_mul] using (hf τ).add (hg τ)

lemma sub (hf : HasQExpansion h f φ) (hg : HasQExpansion h g ψ) :
    HasQExpansion h (fun τ ↦ f τ - g τ) (φ - ψ) := fun τ ↦ by
  simpa [sub_mul] using (hf τ).sub (hg τ)

lemma mul (hf : HasQExpansion h f φ) (hg : HasQExpansion h g ψ) :
    HasQExpansion h (fun τ ↦ f τ * g τ) (φ * ψ) := fun τ ↦ by
  have h1 := (hf τ).summable.norm
  have h2 := (hg τ).summable.norm
  have h3 := (summable_norm_sum_mul_antidiagonal_of_summable_norm h1 h2).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h1 h2, (hf τ).tsum_eq,
    (hg τ).tsum_eq] at h3
  convert! h3 using 2 with m
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hx]
  ring

lemma const (h : ℝ) (c : ℂ) : HasQExpansion h (fun _ ↦ c) (C c) := fun τ ↦ by
  have := hasSum_single (f := fun m ↦ coeff m (C c) * 𝕢 h τ ^ m) 0
    (fun m hm ↦ by simp [coeff_C, hm])
  simpa using this

lemma qParam (h : ℝ) : HasQExpansion h (fun τ ↦ 𝕢 h τ) X := fun τ ↦ by
  have := hasSum_single (f := fun m ↦ coeff m (X : PowerSeries ℂ) * 𝕢 h τ ^ m) 1
    (fun m hm ↦ by simp [coeff_X, hm])
  simpa using this

lemma pow (hf : HasQExpansion h f φ) (n : ℕ) : HasQExpansion h (fun τ ↦ f τ ^ n) (φ ^ n) := by
  induction n with
  | zero => simpa using const h 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

lemma of_qParam_mul (hf : HasQExpansion h (fun τ ↦ 𝕢 h τ * f τ) (X * φ)) :
    HasQExpansion h f φ := fun τ ↦ by
  have h1 := (hasSum_nat_add_iff' 1).mpr (hf τ)
  have hq : 𝕢 h τ ≠ 0 := Periodic.qParam_ne_zero _
  have h2 := h1.mul_left (𝕢 h τ)⁻¹
  simp only [coeff_succ_X_mul, Finset.range_one, Finset.sum_singleton, coeff_zero_X_mul,
    zero_mul, sub_zero, inv_mul_cancel_left₀ hq] at h2
  convert! h2 using 2 with m
  field_simp
  ring

lemma eq_zero (hh : 0 < h) (hf : HasQExpansion h (fun _ ↦ 0) φ) : φ = 0 := by
  ext m
  induction m generalizing φ with
  | zero => exact (tendsto_nhds_unique tendsto_const_nhds (hf.tendsto hh)).symm
  | succ m ih =>
    have h0 : coeff 0 φ = 0 := (tendsto_nhds_unique tendsto_const_nhds (hf.tendsto hh)).symm
    obtain ⟨ψ, rfl⟩ : X ∣ φ := X_dvd_iff.mpr (by simpa using h0)
    have := ih (φ := ψ) (of_qParam_mul (by simpa using hf))
    simpa [coeff_succ_X_mul] using this

lemma unique (hh : 0 < h) (hf : HasQExpansion h f φ) (hg : HasQExpansion h f ψ) : φ = ψ :=
  sub_eq_zero.mp (eq_zero hh (by simpa using hf.sub hg))

lemma of_hasSum_pow {c : ℕ → ℂ} {e : ℕ} (he : e ≠ 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m * (𝕢 h τ ^ e) ^ m) (f τ)) :
    HasQExpansion h f (PowerSeries.mk fun k ↦ if e ∣ k then c (k / e) else 0) := fun τ ↦ by
  have hinj : Injective (fun m : ℕ ↦ e * m) := mul_right_injective₀ he
  rw [← hinj.hasSum_iff]
  · convert hf τ using 2 with m
    simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he), pow_mul]
  · intro k hk
    have : ¬ e ∣ k := fun ⟨m, hm⟩ ↦ hk ⟨m, hm.symm⟩
    simp [this]

lemma of_periodic (hh : 0 < h) (hper : Periodic (f ∘ ofComplex) h) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) : HasQExpansion h f (qExpansion h f) := fun τ ↦ by
  simpa using UpperHalfPlane.hasSum_qExpansion hh hper hhol hbdd τ

end HasQExpansion

lemma hasQExpansion_modularForm {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    HasQExpansion 1 f (qExpansion 1 f) := fun τ ↦
  ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_SL τ

end GlobalTheory
