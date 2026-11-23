import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoBasic
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCutoff

namespace GroundTheory.Automorphic.Sobolev

open MeasureTheory SchwartzMap LineDeriv FourierTransform Real
open scoped ContDiff

noncomputable section

variable {n : ℕ}

theorem fourier_iteratedLineDerivOp_apply (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (∂^{w} f) ξ = (∏ l, (2 * π * Complex.I) * (inner ℝ ξ (w l) : ℂ)) * 𝓕 f ξ := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, fourier_lineDerivOp_eq]
    have hg : (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ x (w 0)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (w 0)).hasTemperateGrowth
    rw [smul_apply, smulLeftCLM_apply_apply hg, ih, Fin.prod_univ_succ]
    simp only [Fin.tail]
    rw [Complex.real_smul]
    simp only [smul_eq_mul]
    ring

section Plancherel

variable {v : EuclideanSpace ℝ (Fin n) → ℂ}

private theorem inner_ev (ξ : EuclideanSpace ℝ (Fin n)) (i : Fin n) : inner ℝ ξ (ev i) = ξ i := by
  simp [ev, EuclideanSpace.inner_single_right]

theorem pdT_eq_iteratedLineDerivOp (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) {k : ℕ}
    (J : Fin k → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    pdT J v x = (∂^{fun l ↦ ev (J l)} (hvc.toSchwartzMap hv)) x := by
  rw [iteratedLineDerivOp_eq_iteratedFDeriv]
  rfl

theorem integrable_norm_sq_schwartz (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Integrable (fun x ↦ ‖g x‖ ^ 2) := by
  have h := (g.memLp 2).integrable_norm_pow (p := 2) two_ne_zero
  simpa using h

theorem norm_sq_fourier_pdT (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {k : ℕ} (J : Fin k → Fin n)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖𝓕 (∂^{fun l ↦ ev (J l)} φ) ξ‖ ^ 2 =
      (∏ l, (2 * π) ^ 2 * ξ (J l) ^ 2) * ‖𝓕 φ ξ‖ ^ 2 := by
  rw [fourier_iteratedLineDerivOp_apply, norm_mul, norm_prod, mul_pow, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [inner_ev, norm_mul, mul_pow]
  have h1 : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h1, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem sum_prod_eq_pow {k : ℕ} (c : Fin n → ℝ) :
    ∑ J : Fin k → Fin n, ∏ l, c (J l) = (∑ i, c i) ^ k := by
  have h := Finset.prod_univ_sum (fun _ : Fin k ↦ (Finset.univ : Finset (Fin n)))
    (fun _ i ↦ c i)
  rw [Fintype.piFinset_univ] at h
  rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem sum_sq_eq_norm_sq (ξ : EuclideanSpace ℝ (Fin n)) : ∑ i, ξ i ^ 2 = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  simp

theorem integral_hsD_sq (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (q : ℕ) :
    ∫ x, hsD q v x ^ 2 = ∫ ξ, ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ q * ‖𝓕 v ξ‖ ^ 2 := by
  set φ := hvc.toSchwartzMap hv
  have hφ : ∀ ξ, (𝓕 φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ = 𝓕 v ξ := fun ξ ↦
    congrFun (fourier_coe φ) ξ
  simp_rw [hsD_sq]
  rw [integral_finsetSum _ fun J _ ↦ ?_]
  swap
  · simp_rw [pdT_eq_iteratedLineDerivOp hv hvc]
    exact integrable_norm_sq_schwartz _
  have h1 : ∀ J : Fin q → Fin n, ∫ x, ‖pdT J v x‖ ^ 2 =
      ∫ ξ, (∏ l, (2 * π) ^ 2 * ξ (J l) ^ 2) * ‖𝓕 φ ξ‖ ^ 2 := fun J ↦ by
    have e : (fun x ↦ ‖pdT J v x‖ ^ 2) = fun x ↦ ‖(∂^{fun l ↦ ev (J l)} φ) x‖ ^ 2 :=
      funext fun x ↦ by rw [pdT_eq_iteratedLineDerivOp hv hvc]
    rw [e, ← integral_norm_sq_fourier]
    simp_rw [norm_sq_fourier_pdT]
  simp_rw [h1]
  rw [← integral_finsetSum _ fun J _ ↦ ?_]
  swap
  · have := integrable_norm_sq_schwartz (𝓕 (∂^{fun l ↦ ev (J l)} φ))
    simpa only [norm_sq_fourier_pdT] using this
  refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
  simp only
  rw [← Finset.sum_mul, sum_prod_eq_pow (fun i ↦ (2 * π) ^ 2 * ξ i ^ 2), ← Finset.mul_sum,
    sum_sq_eq_norm_sq, hφ]

end Plancherel

section Symbol

variable {m : ℕ} {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}

def frozenOp (A : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ) (m : ℕ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ α ∈ A with mabs α = m, a α x₀ * pderiv α v x

theorem fourier_mdir_apply (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (α : Fin n → ℕ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (∂^{mdir α} φ) ξ = (2 * π * Complex.I) ^ mabs α * (mpow α ξ : ℂ) * 𝓕 φ ξ := by
  rw [fourier_iteratedLineDerivOp_apply, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← prod_inner_mdir α ξ]
  push_cast
  ring

theorem prinSymbol_smul (x₀ ξ : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    prinSymbol A a m x₀ (t • ξ) = (t : ℂ) ^ m * prinSymbol A a m x₀ ξ := by
  rw [prinSymbol, prinSymbol, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  rw [Finset.mem_filter] at hα
  have h : mpow α (t • ξ) = t ^ m * mpow α ξ := by
    simp only [mpow, PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [← hα.2]
    rfl
  rw [h]
  push_cast
  ring

theorem continuous_prinSymbol (x₀ : EuclideanSpace ℝ (Fin n)) :
    Continuous (prinSymbol A a m x₀) := by
  unfold prinSymbol mpow
  fun_prop

theorem exists_prinSymbol_lower_bound (hnm : 0 < n ∨ 1 ≤ m) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x₀ ξ ≠ 0) :
    ∃ c > 0, ∀ ξ : EuclideanSpace ℝ (Fin n), c * ‖ξ‖ ^ m ≤ ‖prinSymbol A a m x₀ ξ‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hm : 1 ≤ m := hnm.resolve_left (lt_irrefl 0)
    refine ⟨1, one_pos, fun ξ ↦ ?_⟩
    have : ξ = 0 := Subsingleton.elim _ _
    rw [this, norm_zero, zero_pow (by omega), mul_zero]
    exact norm_nonneg _
  set S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have hu : ‖ev (⟨0, hn⟩ : Fin n)‖ = 1 := norm_ev _
  have hSne : S.Nonempty := ⟨ev ⟨0, hn⟩, by simp [S, hu]⟩
  obtain ⟨u₀, hu₀S, hmin⟩ := hS.exists_isMinOn hSne
    ((continuous_prinSymbol (A := A) (a := a) (m := m) x₀).norm.continuousOn)
  have hu₀ : u₀ ≠ 0 := by
    intro h
    rw [h] at hu₀S
    simp [S] at hu₀S
  refine ⟨‖prinSymbol A a m x₀ u₀‖, norm_pos_iff.2 (hell u₀ hu₀), fun ξ ↦ ?_⟩
  obtain ⟨u, huS, hξu⟩ : ∃ u ∈ S, ξ = ‖ξ‖ • u := by
    by_cases hξ : ξ = 0
    · exact ⟨ev ⟨0, hn⟩, by simp [S, hu], by simp [hξ]⟩
    · refine ⟨‖ξ‖⁻¹ • ξ, ?_, ?_⟩
      · simp [S, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ)]
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hξ), one_smul]
  have h1 : ‖prinSymbol A a m x₀ ξ‖ = ‖ξ‖ ^ m * ‖prinSymbol A a m x₀ u‖ := by
    conv_lhs => rw [hξu]
    rw [prinSymbol_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg ξ)]
  rw [h1, mul_comm]
  exact mul_le_mul_of_nonneg_left (hmin huS) (by positivity)

theorem exists_schwartz_frozenOp {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ x, ψ x = frozenOp A a m x₀ v x) ∧
      ∀ ξ, ‖(𝓕 ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ‖ ^ 2 =
        (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  set φ := hvc.toSchwartzMap hv
  refine ⟨∑ α ∈ A with mabs α = m, a α x₀ • ∂^{mdir α} φ, fun x ↦ ?_, fun ξ ↦ ?_⟩
  · simp only [frozenOp, sum_apply, smul_apply, smul_eq_mul, iteratedLineDerivOp_eq_iteratedFDeriv]
    rfl
  · have hFψ : (𝓕 (∑ α ∈ A with mabs α = m, a α x₀ • ∂^{mdir α} φ) :
        𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ =
        (2 * π * Complex.I) ^ m * prinSymbol A a m x₀ ξ * 𝓕 v ξ := by
      simp only [FourierTransform.fourier_sum, FourierTransform.fourier_smul, sum_apply,
        smul_apply, smul_eq_mul, fourier_mdir_apply, prinSymbol, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α hα ↦ ?_
      rw [Finset.mem_filter] at hα
      rw [hα.2, show (𝓕 φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ = 𝓕 v ξ from
        congrFun (fourier_coe φ) ξ]
      ring
    rw [hFψ, norm_mul, norm_mul, norm_pow]
    have h1 : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [h1]
    ring

theorem integral_norm_sq_frozenOp {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ‖frozenOp A a m x₀ v x‖ ^ 2 =
      ∫ ξ, (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  obtain ⟨ψ, hψ, hFψ⟩ := exists_schwartz_frozenOp (A := A) (a := a) (m := m) hv hvc x₀
  have e : (fun x ↦ ‖frozenOp A a m x₀ v x‖ ^ 2) = fun x ↦ ‖ψ x‖ ^ 2 := funext fun x ↦ by rw [hψ]
  rw [e, ← integral_norm_sq_fourier]
  exact integral_congr_ae (ae_of_all _ fun ξ ↦ hFψ ξ)

theorem integrable_frozen_fourier {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ξ ↦ (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) := by
  obtain ⟨ψ, -, hFψ⟩ := exists_schwartz_frozenOp (A := A) (a := a) (m := m) hv hvc x₀
  refine (integrable_norm_sq_schwartz (𝓕 ψ)).congr (ae_of_all _ fun ξ ↦ ?_)
  exact hFψ ξ

end Symbol

section Helpers

variable {v : EuclideanSpace ℝ (Fin n) → ℂ}

private theorem continuous_pdT' (hv : ContDiff ℝ ∞ v) {k : ℕ} (J : Fin k → Fin n) :
    Continuous (pdT J v) :=
  (continuous_eval_const _).comp (hv.continuous_iteratedFDeriv (by exact_mod_cast le_top))

private theorem pdT_eq_zero' {k : ℕ} (J : Fin k → Fin n) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport v) : pdT J v x = 0 := by
  have : iteratedFDeriv ℝ k v x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_iteratedFDeriv_subset k h)
  rw [pdT_apply, this, zero_apply]

private theorem continuous_hsD' (hv : ContDiff ℝ ∞ v) (k : ℕ) : Continuous (hsD k v) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun J _ ↦ (continuous_pdT' hv J).norm.pow 2)

private theorem hsD_eq_zero' (k : ℕ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport v) :
    hsD k v x = 0 := by
  simp [hsD, pdT_eq_zero' _ hx]

private theorem memLp_hsD' (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (k : ℕ) :
    MemLp (hsD k v) 2 volume :=
  memLp_two_of_continuous_hasCompactSupport (continuous_hsD' hv k) (hvc.mono' fun x hx ↦ by
    by_contra h
    exact hx (hsD_eq_zero' k h))

theorem exists_mdir_eq_ev (α : Fin n → ℕ) :
    ∃ J : Fin (mabs α) → Fin n, ∀ l, mdir α l = ev (J l) := by
  have h : ∀ l, ∃ i, mdir α l = ev i := fun l ↦ by
    have hmem : mdir α l ∈ mdirList α := List.get_mem _ _
    simp only [mdirList, List.mem_flatMap, List.mem_replicate] at hmem
    obtain ⟨i, -, -, hi⟩ := hmem
    exact ⟨i, hi⟩
  choose J hJ using h
  exact ⟨J, hJ⟩

theorem norm_pdT_le_hsD {k : ℕ} (J : Fin k → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖pdT J v x‖ ≤ hsD k v x := by
  rw [hsD]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun J ↦ ‖pdT J v x‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
    (Finset.mem_univ J)

theorem norm_pderiv_le_hsD (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖pderiv α v x‖ ≤ hsD (mabs α) v x := by
  obtain ⟨J, hJ⟩ := exists_mdir_eq_ev α
  have : pderiv α v x = pdT J v x := by
    rw [pderiv_eq_dT, pdT, dT_apply, dT_apply]
    congr 1
    exact funext hJ
  rw [this]
  exact norm_pdT_le_hsD J x

private theorem pderiv_eq_zero' (α : Fin n → ℕ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport v) : pderiv α v x = 0 := by
  have h := norm_pderiv_le_hsD (v := v) α x
  rw [hsD_eq_zero' _ hx] at h
  exact norm_le_zero_iff.1 h

private theorem continuous_pderiv' (hv : ContDiff ℝ ∞ v) (α : Fin n → ℕ) :
    Continuous (pderiv α v) :=
  (continuous_eval_const _).comp (hv.continuous_iteratedFDeriv (by exact_mod_cast le_top))

end Helpers

section Estimate

variable {m : ℕ} {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}

theorem l2Norm_derivative_le_frozen_operator {c : ℝ} (hc : 0 < c) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hσ : ∀ ξ : EuclideanSpace ℝ (Fin n), c * ‖ξ‖ ^ m ≤ ‖prinSymbol A a m x₀ ξ‖)
    {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    l2n (hsD m v) ≤ c⁻¹ * l2n (fun x ↦ ‖frozenOp A a m x₀ v x‖) := by
  have hP : MemLp (fun x ↦ ‖frozenOp A a m x₀ v x‖) 2 volume := by
    refine memLp_two_of_continuous_hasCompactSupport ?_ (hvc.mono' fun x hx ↦ ?_)
    · exact (continuous_finsetSum _ fun α _ ↦ continuous_const.mul
        (continuous_pderiv' hv α)).norm
    · by_contra h
      apply hx
      simp [frozenOp, pderiv_eq_zero' _ h]
  rw [l2Norm_eq_sqrt_integral_sq (memLp_hsD' hv hvc m), l2Norm_eq_sqrt_integral_sq hP,
    integral_hsD_sq hv hvc, integral_norm_sq_frozenOp hv hvc x₀]
  have hci : c⁻¹ = Real.sqrt ((c⁻¹) ^ 2) := (Real.sqrt_sq (inv_nonneg.2 hc.le)).symm
  rw [hci, ← Real.sqrt_mul (sq_nonneg _), ← integral_const_mul]
  refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (ae_of_all _ fun ξ ↦ by positivity)
    ((integrable_frozen_fourier hv hvc x₀).const_mul _) (ae_of_all _ fun ξ ↦ ?_))
  have h2 : ‖ξ‖ ^ m ≤ c⁻¹ * ‖prinSymbol A a m x₀ ξ‖ := by
    rw [le_inv_mul_iff₀ hc]
    exact hσ ξ
  have h3 : (‖ξ‖ ^ m) ^ 2 ≤ (c⁻¹ * ‖prinSymbol A a m x₀ ξ‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  calc ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ m * ‖𝓕 v ξ‖ ^ 2
      = (2 * π) ^ (2 * m) * (‖ξ‖ ^ m) ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring
    _ ≤ (2 * π) ^ (2 * m) * (c⁻¹ * ‖prinSymbol A a m x₀ ξ‖) ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by gcongr
    _ = (c⁻¹) ^ 2 * ((2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) := by ring

theorem elliptic_estimate (hnm : 0 < n ∨ 1 ≤ m) (hA : ∀ α ∈ A, mabs α ≤ m)
    (ha : ∀ α ∈ A, Continuous (a α)) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x₀ ξ ≠ 0) :
    ∃ R₀ > 0, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ v : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ v →
      HasCompactSupport v → tsupport v ⊆ Metric.ball x₀ R₀ →
      l2n (hsD m v) ≤ C₀ * (l2n (fun x ↦ ‖diffOp A a v x‖) +
        ∑ j ∈ Finset.range m, l2n (hsD j v)) := by
  obtain ⟨c, hc, hσ⟩ := exists_prinSymbol_lower_bound hnm hell
  set N : ℝ := (A.card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Metric.closedBall x₀ 1, ∀ α ∈ A, ‖a α x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ 1).exists_bound_of_continuousOn
      (f := fun x ↦ ∑ α ∈ A, ‖a α x‖)
      (continuous_finsetSum _ fun α hα ↦ (ha α hα).norm).continuousOn
    refine ⟨M, fun x hx α hα ↦ ?_⟩
    have h := hM x hx
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at h
    exact (Finset.single_le_sum (f := fun β ↦ ‖a β x‖) (fun β _ ↦ norm_nonneg (a β x)) hα).trans h
  set M' := max M 0
  have hM' : 0 ≤ M' := le_max_right _ _
  set ε := c / (2 * (N + 1))
  have hε : 0 < ε := by positivity
  have hev : ∀ᶠ x in nhds x₀, ∀ α ∈ A, ‖a α x - a α x₀‖ < ε := by
    rw [Filter.eventually_all_finset]
    intro α hα
    filter_upwards [Metric.tendsto_nhds.1 ((ha α hα).tendsto x₀) ε hε] with x hx
    rwa [dist_eq_norm] at hx
  obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨min δ 1, lt_min hδ one_pos, 2 * c⁻¹ * max 1 (M' * N), by positivity,
    fun v hv hvc hsupp ↦ ?_⟩
  set X := l2n (hsD m v)
  set Y := ∑ j ∈ Finset.range m, l2n (hsD j v)
  set Z := l2n (fun x ↦ ‖diffOp A a v x‖)
  have hX0 : 0 ≤ X := l2Norm_nonneg_alt _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ ↦ l2Norm_nonneg_alt _
  have hZ0 : 0 ≤ Z := l2Norm_nonneg_alt _

  have hpt : ∀ x, ‖frozenOp A a m x₀ v x‖ ≤ ‖diffOp A a v x‖ + (ε * N) * hsD m v x +
      (M' * N) * ∑ j ∈ Finset.range m, hsD j v x := by
    intro x
    have hsplit : diffOp A a v x = (∑ α ∈ A with mabs α = m, a α x * pderiv α v x) +
        ∑ α ∈ A with ¬ mabs α = m, a α x * pderiv α v x :=
      (Finset.sum_filter_add_sum_filter_not A _ _).symm
    have hfz : frozenOp A a m x₀ v x = diffOp A a v x -
        (∑ α ∈ A with mabs α = m, (a α x - a α x₀) * pderiv α v x) -
        ∑ α ∈ A with ¬ mabs α = m, a α x * pderiv α v x := by
      rw [hsplit, frozenOp]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    have h1 : ∀ α ∈ A, ‖(a α x - a α x₀) * pderiv α v x‖ ≤ ε * hsD (mabs α) v x := by
      intro α hα
      by_cases hx : x ∈ tsupport v
      · have hxb := hsupp hx
        rw [Metric.mem_ball] at hxb
        rw [norm_mul]
        exact mul_le_mul (hδε (lt_of_lt_of_le hxb (min_le_left _ _)) α hα).le
          (norm_pderiv_le_hsD α x) (norm_nonneg _) hε.le
      · rw [pderiv_eq_zero' α hx, mul_zero, norm_zero]
        exact mul_nonneg hε.le (hsD_nonneg _ _ _)
    have h2 : ∀ α ∈ A, ‖a α x * pderiv α v x‖ ≤ M' * hsD (mabs α) v x := by
      intro α hα
      by_cases hx : x ∈ tsupport v
      · have hxb := hsupp hx
        rw [Metric.mem_ball] at hxb
        have hxc : x ∈ Metric.closedBall x₀ 1 :=
          Metric.mem_closedBall.2 (lt_of_lt_of_le hxb (min_le_right _ _)).le
        rw [norm_mul]
        exact mul_le_mul ((hM x hxc α hα).trans (le_max_left _ _))
          (norm_pderiv_le_hsD α x) (norm_nonneg _) hM'
      · rw [pderiv_eq_zero' α hx, mul_zero, norm_zero]
        exact mul_nonneg hM' (hsD_nonneg _ _ _)
    have h3 : ‖∑ α ∈ A with mabs α = m, (a α x - a α x₀) * pderiv α v x‖ ≤
        (ε * N) * hsD m v x := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ α ∈ A with mabs α = m, ‖(a α x - a α x₀) * pderiv α v x‖
          ≤ ∑ α ∈ A with mabs α = m, ε * hsD m v x := by
            refine Finset.sum_le_sum fun α hα ↦ ?_
            rw [Finset.mem_filter] at hα
            have := h1 α hα.1
            rwa [hα.2] at this
        _ ≤ ∑ α ∈ A, ε * hsD m v x :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ ↦ mul_nonneg hε.le (hsD_nonneg _ _ _)
        _ = (ε * N) * hsD m v x := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have h4 : ‖∑ α ∈ A with ¬ mabs α = m, a α x * pderiv α v x‖ ≤
        (M' * N) * ∑ j ∈ Finset.range m, hsD j v x := by
      refine (norm_sum_le _ _).trans ?_
      have hS : 0 ≤ ∑ j ∈ Finset.range m, hsD j v x :=
        Finset.sum_nonneg fun _ _ ↦ hsD_nonneg _ _ _
      calc ∑ α ∈ A with ¬ mabs α = m, ‖a α x * pderiv α v x‖
          ≤ ∑ α ∈ A with ¬ mabs α = m, M' * ∑ j ∈ Finset.range m, hsD j v x := by
            refine Finset.sum_le_sum fun α hα ↦ ?_
            rw [Finset.mem_filter] at hα
            refine (h2 α hα.1).trans (mul_le_mul_of_nonneg_left ?_ hM')
            have hlt : mabs α < m := lt_of_le_of_ne (hA α hα.1) hα.2
            exact Finset.single_le_sum (f := fun j ↦ hsD j v x) (fun _ _ ↦ hsD_nonneg _ _ _)
              (Finset.mem_range.2 hlt)
        _ ≤ ∑ α ∈ A, M' * ∑ j ∈ Finset.range m, hsD j v x :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ ↦ mul_nonneg hM' hS
        _ = (M' * N) * ∑ j ∈ Finset.range m, hsD j v x := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    rw [hfz]
    calc ‖diffOp A a v x - (∑ α ∈ A with mabs α = m, (a α x - a α x₀) * pderiv α v x) -
          ∑ α ∈ A with ¬ mabs α = m, a α x * pderiv α v x‖
        ≤ ‖diffOp A a v x‖ + ‖∑ α ∈ A with mabs α = m, (a α x - a α x₀) * pderiv α v x‖ +
          ‖∑ α ∈ A with ¬ mabs α = m, a α x * pderiv α v x‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by gcongr

  have hDv : MemLp (fun x ↦ ‖diffOp A a v x‖) 2 volume := by
    refine memLp_two_of_continuous_hasCompactSupport ?_ (hvc.mono' fun x hx ↦ ?_)
    · exact (continuous_finsetSum _ fun α hα ↦ (ha α hα).mul (continuous_pderiv' hv α)).norm
    · by_contra h
      apply hx
      simp [diffOp, pderiv_eq_zero' _ h]
  have hHm := memLp_hsD' hv hvc m
  have hHs : MemLp (fun x ↦ ∑ j ∈ Finset.range m, hsD j v x) 2 volume := by
    exact memLp_finsetSum (Finset.range m) fun j _ ↦ memLp_hsD' hv hvc j
  have hR1 : MemLp (fun x ↦ (ε * N) * hsD m v x) 2 volume := hHm.const_mul _
  have hR2 : MemLp (fun x ↦ (M' * N) * ∑ j ∈ Finset.range m, hsD j v x) 2 volume :=
    hHs.const_mul _
  have hfrozen : l2n (fun x ↦ ‖frozenOp A a m x₀ v x‖) ≤ Z + (ε * N) * X + (M' * N) * Y := by
    have hR : MemLp (fun x ↦ ‖diffOp A a v x‖ + (ε * N) * hsD m v x +
        (M' * N) * ∑ j ∈ Finset.range m, hsD j v x) 2 volume := (hDv.add hR1).add hR2
    have hFc : Continuous (fun x ↦ ‖frozenOp A a m x₀ v x‖) :=
      (continuous_finsetSum _ fun α _ ↦ continuous_const.mul (continuous_pderiv' hv α)).norm
    refine (l2Norm_le_of_abs_le hR hFc.aestronglyMeasurable fun x ↦ ?_).trans ?_
    · rw [abs_of_nonneg (norm_nonneg _)]
      exact hpt x
    refine (l2Norm_add_le_alt (hDv.add hR1) hR2).trans ?_
    refine (add_le_add (l2Norm_add_le_alt hDv hR1) le_rfl).trans ?_
    rw [l2Norm_const_mul, l2Norm_const_mul, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have hY : l2n (fun x ↦ ∑ j ∈ Finset.range m, hsD j v x) ≤ Y :=
      l2Norm_finset_sum_le _ _ fun j _ ↦ memLp_hsD' hv hvc j
    gcongr
  have hmain : X ≤ c⁻¹ * (Z + ε * N * X + M' * N * Y) := (l2Norm_derivative_le_frozen_operator hc hσ hv hvc).trans
    (mul_le_mul_of_nonneg_left hfrozen (inv_nonneg.2 hc.le))

  have hεN : c⁻¹ * (ε * N) ≤ 1 / 2 := by
    have : c⁻¹ * (ε * N) = N / (2 * (N + 1)) := by
      simp only [ε]
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) two_pos]
    linarith
  have e1 : c⁻¹ * (Z + ε * N * X + M' * N * Y) =
      c⁻¹ * Z + (c⁻¹ * (ε * N)) * X + c⁻¹ * (M' * N * Y) := by ring
  have e2 : (c⁻¹ * (ε * N)) * X ≤ (1 / 2) * X := mul_le_mul_of_nonneg_right hεN hX0
  have hX : X ≤ 2 * c⁻¹ * (Z + (M' * N) * Y) := by
    have h6 : X ≤ c⁻¹ * Z + (1 / 2) * X + c⁻¹ * (M' * N * Y) := by
      rw [e1] at hmain; linarith
    have e3 : 2 * c⁻¹ * (Z + M' * N * Y) = 2 * (c⁻¹ * Z) + 2 * (c⁻¹ * (M' * N * Y)) := by ring
    rw [e3]; linarith
  calc X ≤ 2 * c⁻¹ * (Z + (M' * N) * Y) := hX
    _ ≤ 2 * c⁻¹ * (max 1 (M' * N) * Z + max 1 (M' * N) * Y) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact le_mul_of_one_le_left hZ0 (le_max_left _ _)
        · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hY0
    _ = 2 * c⁻¹ * max 1 (M' * N) * (Z + Y) := by ring

end Estimate

section Pointwise

variable {v : EuclideanSpace ℝ (Fin n) → ℂ}

theorem integrable_fourier_weight (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (q : ℕ) :
    Integrable (fun ξ ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ q * ‖𝓕 v ξ‖ ^ 2) := by
  set φ := hvc.toSchwartzMap hv
  have hint : Integrable (fun ξ ↦ ∑ J : Fin q → Fin n,
      ‖(𝓕 (∂^{fun l ↦ ev (J l)} φ) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ‖ ^ 2) :=
    integrable_finsetSum _ fun J _ ↦ integrable_norm_sq_schwartz _
  refine hint.congr (ae_of_all _ fun ξ ↦ ?_)
  simp only [norm_sq_fourier_pdT]
  rw [← Finset.sum_mul, sum_prod_eq_pow (fun i ↦ (2 * π) ^ 2 * ξ i ^ 2), ← Finset.mul_sum,
    sum_sq_eq_norm_sq, show (𝓕 φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ = 𝓕 v ξ from
      congrFun (fourier_coe φ) ξ]

private theorem one_add_pow_le (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    (1 + s) ^ k ≤ 2 ^ k * (1 + s ^ k) := by
  rcases le_total s 1 with h | h
  · calc (1 + s) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + s ^ k) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + s) ^ k ≤ (2 * s) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * s ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + s ^ k) := by gcongr; linarith

theorem integrable_inv_one_add_weight {σ : ℕ} (hσ : n < 2 * σ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) ↦ (1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ)⁻¹) := by
  have hr : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℕ) : ℝ) < ((2 * σ : ℕ) : ℝ) := by
    rw [finrank_euclideanSpace_fin]
    exact_mod_cast hσ
  refine ((integrable_one_add_norm hr).const_mul ((2 : ℝ) ^ (2 * σ))).mono' ?_
    (ae_of_all _ fun ξ ↦ ?_)
  · exact (Continuous.inv₀ (by fun_prop : Continuous fun ξ : EuclideanSpace ℝ (Fin n) ↦
      1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ) fun ξ ↦ by positivity).aestronglyMeasurable
  · have h2π : 1 ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
    have hW : ‖ξ‖ ^ (2 * σ) ≤ ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ := by
      rw [pow_mul, mul_pow]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ h2π)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast]
    have hpos : 0 < (1 + ‖ξ‖) ^ (2 * σ) := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, inv_mul_le_iff₀ (by positivity)]
    have key : (1 + ‖ξ‖) ^ (2 * σ) ≤ 2 ^ (2 * σ) * (1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ) :=
      calc (1 + ‖ξ‖) ^ (2 * σ) ≤ 2 ^ (2 * σ) * (1 + ‖ξ‖ ^ (2 * σ)) :=
            one_add_pow_le _ (norm_nonneg _) _
        _ ≤ 2 ^ (2 * σ) * (1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ) := by gcongr
    exact key.trans_eq (mul_comm _ _)

private theorem le_sqrt_of_forall_le {X a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t > 0, X ≤ (t * a + t⁻¹ * b) / 2) : X ≤ Real.sqrt (a * b) := by
  rcases ha.eq_or_lt with ha0 | hapos
  · subst ha0
    rw [zero_mul, Real.sqrt_zero]
    by_contra hX
    push Not at hX
    have ht : 0 < b / X + 1 := by positivity
    have h1 := h (b / X + 1) ht
    rw [mul_zero, zero_add] at h1
    have h2 : (b / X + 1)⁻¹ * b < X := by
      rw [inv_mul_lt_iff₀ ht, add_mul, div_mul_cancel₀ _ hX.ne', one_mul]
      linarith
    have h3 : 0 ≤ (b / X + 1)⁻¹ * b := by positivity
    linarith
  rcases hb.eq_or_lt with hb0 | hbpos
  · subst hb0
    rw [mul_zero, Real.sqrt_zero]
    by_contra hX
    push Not at hX
    have := h (X / a) (div_pos hX hapos)
    rw [mul_zero, add_zero, div_mul_cancel₀ _ hapos.ne'] at this
    linarith
  · set t := Real.sqrt (b / a)
    have ht : 0 < t := Real.sqrt_pos.2 (div_pos hbpos hapos)
    have h1 := h t ht
    have e1 : t * a = Real.sqrt (a * b) := by
      rw [show t * a = Real.sqrt (b / a) * Real.sqrt (a ^ 2) by
        rw [Real.sqrt_sq hapos.le], ← Real.sqrt_mul (div_nonneg hbpos.le hapos.le)]
      congr 1
      field_simp
    have ht2 : t ^ 2 = b / a := Real.sq_sqrt (div_nonneg hbpos.le hapos.le)
    have e2 : t⁻¹ * b = Real.sqrt (a * b) := by
      rw [← e1]
      have hb' : b = t ^ 2 * a := by rw [ht2]; field_simp
      rw [hb']
      field_simp
    rw [e1, e2] at h1
    linarith

theorem sobolev_pointwise : ∃ σ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EuclideanSpace ℝ (Fin n) → ℂ,
    ContDiff ℝ ∞ w → HasCompactSupport w → ∀ x,
      ‖w x‖ ≤ C * (l2n (hsD 0 w) + l2n (hsD σ w)) := by
  set σ := n / 2 + 1
  have hσ : n < 2 * σ := by omega
  set W : EuclideanSpace ℝ (Fin n) → ℝ := fun ξ ↦ 1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ
  have hWpos : ∀ ξ, 0 < W ξ := fun ξ ↦ by positivity
  set I₁ := ∫ ξ, (W ξ)⁻¹
  have hI₁int : Integrable (fun ξ ↦ (W ξ)⁻¹) := integrable_inv_one_add_weight hσ
  have hI₁ : 0 ≤ I₁ := integral_nonneg fun ξ ↦ (inv_pos.2 (hWpos ξ)).le
  refine ⟨σ, Real.sqrt I₁, Real.sqrt_nonneg _, fun w hw hwc x ↦ ?_⟩
  set φ := hwc.toSchwartzMap hw
  have hFw : ∀ ξ, (𝓕 φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ = 𝓕 w ξ := fun ξ ↦
    congrFun (fourier_coe φ) ξ
  have hFint : Integrable (𝓕 w) := (𝓕 φ).integrable.congr (ae_of_all _ hFw)
  have hinv : w x = 𝓕⁻ (𝓕 w) x := by
    rw [hw.continuous.fourierInv_fourier_eq (φ.integrable) hFint]
  have hx1 : ‖w x‖ ≤ ∫ ξ, ‖𝓕 w ξ‖ := by
    rw [hinv, Real.fourierInv_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
    simp only [Circle.norm_smul]
  set I₂ := ∫ ξ, W ξ * ‖𝓕 w ξ‖ ^ 2
  have hsq0 := integrable_fourier_weight hw hwc 0
  have hsqσ := integrable_fourier_weight hw hwc σ
  have hWint : Integrable (fun ξ ↦ W ξ * ‖𝓕 w ξ‖ ^ 2) := by
    refine (hsq0.add hsqσ).congr (ae_of_all _ fun ξ ↦ ?_)
    simp only [W, Pi.add_apply, pow_zero, one_mul]
    ring
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun ξ ↦ mul_nonneg (hWpos ξ).le (sq_nonneg _)
  have hI₂ : I₂ = l2n (hsD 0 w) ^ 2 + l2n (hsD σ w) ^ 2 := by
    rw [l2Norm_eq_sqrt_integral_sq (memLp_hsD' hw hwc 0), l2Norm_eq_sqrt_integral_sq (memLp_hsD' hw hwc σ),
      Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
      Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _), integral_hsD_sq hw hwc,
      integral_hsD_sq hw hwc, ← integral_add hsq0 hsqσ]
    refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
    simp only [W, pow_zero, one_mul]
    ring
  have hamgm : ∫ ξ, ‖𝓕 w ξ‖ ≤ Real.sqrt (I₁ * I₂) := by
    refine le_sqrt_of_forall_le hI₁ hI₂0 fun t ht ↦ ?_
    have hR : Integrable (fun ξ ↦ (t * (W ξ)⁻¹ + t⁻¹ * (W ξ * ‖𝓕 w ξ‖ ^ 2)) / 2) :=
      ((hI₁int.const_mul t).add (hWint.const_mul t⁻¹)).div_const 2
    have hpt : ∀ ξ, ‖𝓕 w ξ‖ ≤ (t * (W ξ)⁻¹ + t⁻¹ * (W ξ * ‖𝓕 w ξ‖ ^ 2)) / 2 := fun ξ ↦ by
      have hW := hWpos ξ
      have key : (t * (W ξ)⁻¹ + t⁻¹ * (W ξ * ‖𝓕 w ξ‖ ^ 2)) / 2 - ‖𝓕 w ξ‖ =
          (t - W ξ * ‖𝓕 w ξ‖) ^ 2 / (2 * t * W ξ) := by
        field_simp
        ring
      have : 0 ≤ (t - W ξ * ‖𝓕 w ξ‖) ^ 2 / (2 * t * W ξ) := by positivity
      linarith
    calc ∫ ξ, ‖𝓕 w ξ‖ ≤ ∫ ξ, (t * (W ξ)⁻¹ + t⁻¹ * (W ξ * ‖𝓕 w ξ‖ ^ 2)) / 2 :=
          integral_mono hFint.norm hR hpt
      _ = (t * I₁ + t⁻¹ * I₂) / 2 := by
          rw [integral_div, integral_add (hI₁int.const_mul t) (hWint.const_mul t⁻¹),
            integral_const_mul, integral_const_mul]
  have hs : Real.sqrt I₂ ≤ l2n (hsD 0 w) + l2n (hsD σ w) := by
    rw [hI₂, Real.sqrt_le_left (add_nonneg (l2Norm_nonneg_alt _) (l2Norm_nonneg_alt _))]
    have h0 := l2Norm_nonneg_alt (hsD 0 w)
    have hσ' := l2Norm_nonneg_alt (hsD σ w)
    nlinarith
  calc ‖w x‖ ≤ ∫ ξ, ‖𝓕 w ξ‖ := hx1
    _ ≤ Real.sqrt (I₁ * I₂) := hamgm
    _ = Real.sqrt I₁ * Real.sqrt I₂ := Real.sqrt_mul hI₁ _
    _ ≤ Real.sqrt I₁ * (l2n (hsD 0 w) + l2n (hsD σ w)) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)

end Pointwise

end

end GroundTheory.Automorphic.Sobolev
