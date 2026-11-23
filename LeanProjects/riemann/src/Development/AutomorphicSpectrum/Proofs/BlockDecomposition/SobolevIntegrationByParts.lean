import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfContinuousOn

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.FcCalc.Ibp

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open GlobalTheory.CompanionTheory.WeightIbp (isOpen_invertible val_mem_invertible weight_ibp)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def psi (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem psi_contDiff : ContDiff ℝ ∞ psi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem psi_eq_one {t : ℝ} (h : t ≤ 1) : psi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem psi_eq_zero {t : ℝ} (h : 2 ≤ t) : psi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem exists_deriv_bound : ∃ D : ℝ, ∀ t, ‖deriv psi t‖ ≤ D := by
  have hc : Continuous (deriv psi) := psi_contDiff.continuous_deriv (by simp)
  refine HasCompactSupport.exists_bound_of_continuous
    (HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun t ht => ?_) hc
  rcases lt_or_ge t 1 with h | h
  · have e : psi =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs using psi_eq_one (le_of_lt hs)
    rw [e.deriv_eq]; simp
  · have h2 : 2 < t := by
      by_contra hn
      exact ht ⟨h, not_lt.1 hn⟩
    have e : psi =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h2] with s hs using psi_eq_zero (le_of_lt hs)
    rw [e.deriv_eq]; simp

def chi (R : ℝ) (y : Mat n) : ℝ := psi (R⁻¹ * lg y)

theorem chi_smooth (hL : LgFacts) (R : ℝ) : ContDiffOn ℝ ∞ (chi R : Mat n → ℝ) (GLs n) :=
  psi_contDiff.comp_contDiffOn (contDiffOn_const.mul (hL n).2.2.2.1)

theorem chi_cpt {R : ℝ} (hR : 0 < R) : Cpt (chi R : Mat n → ℝ) := by
  refine ⟨2 * R, fun y _ h => psi_eq_zero ?_⟩
  rw [inv_mul_eq_div, le_div_iff₀ hR]
  exact h.le

theorem chi_eq_one {R : ℝ} (hR : 0 < R) {y : Mat n} (h : lg y ≤ R) : chi R y = 1 := by
  refine psi_eq_one ?_
  rw [inv_mul_eq_div, div_le_iff₀ hR]
  linarith

theorem chi_abs_le (R : ℝ) (y : Mat n) : ‖((chi R y : ℝ) : ℂ)‖ ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (2 - R⁻¹ * lg y)
  have h1 := Real.smoothTransition.le_one (2 - R⁻¹ * lg y)
  have e : chi R y = Real.smoothTransition (2 - R⁻¹ * lg y) := rfl
  rw [Complex.norm_real, e, Real.norm_of_nonneg h0]
  exact h1

theorem chi_fderiv_le (hL : LgFacts) {D : ℝ} (hD : ∀ t, ‖deriv psi t‖ ≤ D) {R : ℝ} (hR : 0 < R) {x : Mat n}
    (hx : x ∈ GLs n) (v : Mat n) : |fderiv ℝ (chi R) x v| ≤ D * (R⁻¹ * |fderiv ℝ lg x v|) := by
  have hlg : HasFDerivAt (lg : Mat n → ℝ) (fderiv ℝ lg x) x :=
    (((hL n).2.2.2.1.contDiffAt (isOpen_invertible.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hp : HasDerivAt psi (deriv psi (R⁻¹ * lg x)) (R⁻¹ * lg x) :=
    ((psi_contDiff.differentiable (by simp)) _).hasDerivAt
  have h := (hp.comp_hasFDerivAt x (hlg.const_mul R⁻¹)).fderiv
  have e : fderiv ℝ (chi R) x v = deriv psi (R⁻¹ * lg x) * (R⁻¹ * fderiv ℝ lg x v) := by
    have e' : chi R = psi ∘ fun y : Mat n => R⁻¹ * lg y := rfl
    rw [e']
    exact (DFunLike.congr_fun h v).trans rfl
  rw [e, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR)]
  exact mul_le_mul_of_nonneg_right (hD _) (by positivity)

theorem chi_continuous (hL : LgFacts) (R : ℝ) : Continuous fun y : G n => ((chi R y.val : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    ((chi_smooth hL R).continuousOn.comp_continuous Units.continuous_val val_mem_invertible)

section Lim

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))

theorem tendsto_chi (hL : LgFacts) {h : G n → ℂ} (hh : Integrable h μ) :
    Tendsto (fun k : ℕ => ∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * h y ∂μ) atTop (𝓝 (∫ y, h y ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun y => ‖h y‖) (fun k => ?_) hh.norm (fun k => ?_) ?_
  · exact (chi_continuous hL _).aestronglyMeasurable.mul hh.1
  · refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (chi_abs_le _ _)
  · refine Eventually.of_forall fun y => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈lg y.val⌉₊] with k hk
    have h1 : lg y.val ≤ (k : ℝ) + 1 := by
      have := (Nat.le_ceil (lg y.val)).trans (Nat.cast_le.2 hk)
      linarith
    rw [chi_eq_one (by positivity) h1]
    simp

theorem tendsto_chi_deriv (hL : LgFacts) {X : Mat n} {C : ℝ} (hC : ∀ x ∈ GLs n, |fderiv ℝ lg x (x * X)| ≤ C)
    {h : G n → ℂ} (hh : Integrable h μ) :
    Tendsto (fun k : ℕ => ∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y ∂μ) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := exists_deriv_bound
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hC0 : ∀ x ∈ GLs n, 0 ≤ C := fun x hx => (abs_nonneg _).trans (hC x hx)
  have hC1 : 0 ≤ C := hC0 _ (val_mem_invertible (1 : G n))
  have hb : ∀ k : ℕ, ‖∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y ∂μ‖ ≤
      (D * C * ∫ y, ‖h y‖ ∂μ) * ((k : ℝ) + 1)⁻¹ := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have := norm_integral_le_of_norm_le (μ := μ)
      (f := fun y : G n => ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y)
      (hh.norm.const_mul (D * (((k : ℝ) + 1)⁻¹ * C)))
      (Eventually.of_forall fun y => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (chi_fderiv_le hL hD hk (val_mem_invertible y) _).trans ?_
        gcongr
        exact hC _ (val_mem_invertible y))
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul]
    ring
  refine squeeze_zero_norm hb ?_
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (D * C * ∫ y, ‖h y‖ ∂μ)
  simpa [one_div] using this

end Lim

section Pair

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_coeff (X : Mat n) : ∃ c : Bool × Fin n × Fin n → ℝ, X = ∑ p, c p • bs p := by
  refine ⟨fun p => if p.1 then (X p.2.1 p.2.2).re else (X p.2.1 p.2.2).im, ?_⟩
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_prod_type, Fintype.sum_bool, bs, Matrix.single_apply]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_and]

theorem Rd_expand (f : Mat n → V) {X : Mat n} {c : Bool × Fin n × Fin n → ℝ} (h : X = ∑ p, c p • bs p) (g : Mat n) :
    Rd X f g = ∑ p, c p • Rd (bs p) f g := by
  simp only [Rd]
  rw [h, Matrix.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_smul, map_smul]

theorem lg_bound (hL : LgFacts) (X : Mat n) : ∃ C : ℝ, ∀ x ∈ GLs n, |fderiv ℝ lg x (x * X)| ≤ C := by
  obtain ⟨c, hc⟩ := exists_coeff X
  obtain ⟨C, hC⟩ := (hL n).2.2.2.2.2.2
  refine ⟨∑ p, |c p| * C, fun x hx => ?_⟩
  have e : fderiv ℝ lg x (x * X) = ∑ p, c p * fderiv ℝ lg x (x * bs p) := by
    rw [hc, Matrix.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_smul, map_smul, smul_eq_mul]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x hx p) (abs_nonneg _)

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)}

theorem memLp_Rd {f : Mat n → V} (hf : Sob μ f) (X : Mat n) : MemLp (fun y : G n => Rd X f y.val) 2 μ := by
  obtain ⟨c, hc⟩ := exists_coeff X
  have e : (fun y : G n => Rd X f y.val) = fun y : G n => ∑ p, c p • Rd (bs p) f y.val :=
    funext fun y => Rd_expand f hc y.val
  rw [e]
  exact memLp_finset_sum _ fun p _ => (hf.2 [p]).const_smul (c p)

theorem memLp_self {f : Mat n → V} (hf : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []

theorem integrable_pair {a b : G n → V} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun y => ⟪a y, b y⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)).congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem inner_cls {a b : Mat n → V} (ha : MemLp (fun y : G n => a y.val) 2 μ)
    (hb : MemLp (fun y : G n => b y.val) 2 μ) :
    ⟪cls μ a, cls μ b⟫_ℂ = ∫ y : G n, ⟪a y.val, b y.val⟫_ℂ ∂μ := by
  simp only [cls, dif_pos ha, dif_pos hb]
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

end Pair

theorem ibpSob : IbpSob := by
  intro n _ _ μ _ V _ _ hL _ hR f f' hf hf' X
  obtain ⟨C, hC⟩ := lg_bound hL X
  have m0 := memLp_self hf
  have m0' := memLp_self hf'
  have m1 := memLp_Rd hf X
  have m1' := memLp_Rd hf' X
  rw [inner_cls m1 m0', inner_cls m0 m1']
  have iA := integrable_pair m0 m1'
  have iB := integrable_pair m1 m0'
  have iC := integrable_pair m0 m0'
  have tA := tendsto_chi μ hL iA
  have tB := tendsto_chi μ hL iB
  have tC := tendsto_chi_deriv μ hL hC iC
  have key : ∀ k : ℕ, ∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * ⟪f y.val, Rd X f' y.val⟫_ℂ ∂μ =
      -(∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * ⟪Rd X f y.val, f' y.val⟫_ℂ ∂μ) -
        ∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * ⟪f y.val, f' y.val⟫_ℂ ∂μ :=
    fun k => weight_ibp hR hL μ f' f (chi ((k : ℝ) + 1)) hf'.1 hf.1 (chi_smooth hL _) (chi_cpt (by positivity)) X
  have tA' := (tB.neg.sub tC).congr fun k => (key k).symm
  have e := tendsto_nhds_unique tA tA'
  rw [e, sub_zero, neg_neg]

end GlobalTheory.CompanionTheory.FcCalc.Ibp
