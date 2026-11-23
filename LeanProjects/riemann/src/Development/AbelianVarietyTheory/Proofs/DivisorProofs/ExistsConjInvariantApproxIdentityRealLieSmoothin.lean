import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.AutGrowth.ApproxId

theorem tendsto_integral_of_concentrate {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] {ν : Measure V}
    {f : V → ℂ} {x₀ : V} (hf : ContinuousAt f x₀) (β : ℕ → V → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (h0 : ∀ n x, 0 ≤ β n x) (h1 : ∀ n, ∫ x, β n x ∂ν = 1) (hs : ∀ n x, β n x ≠ 0 → dist x x₀ < r n)
    (hi : ∀ n, Integrable (β n) ν) (hfi : ∀ n, Integrable (fun x => (β n x : ℂ) * f x) ν) :
    Tendsto (fun n => ∫ x, (β n x : ℂ) * f x ∂ν) atTop (𝓝 (f x₀)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hf (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hr) δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hrn : r n < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have e1 : ∫ x, (β n x : ℂ) * f x₀ ∂ν = f x₀ := by
    rw [integral_mul_const, integral_complex_ofReal, h1 n]; simp
  have e2 : ∫ x, (β n x : ℂ) * f x ∂ν - f x₀ = ∫ x, (β n x : ℂ) * (f x - f x₀) ∂ν := by
    conv_lhs => rw [← e1]
    refine (integral_sub (hfi n) ((hi n).ofReal.mul_const (f x₀))).symm.trans ?_
    congr 1; funext x; rw [mul_sub]; rfl
  rw [dist_eq_norm, e2]
  calc ‖∫ x, (β n x : ℂ) * (f x - f x₀) ∂ν‖ ≤ ∫ x, β n x * (ε / 2) ∂ν := by
        refine norm_integral_le_of_norm_le ((hi n).mul_const _) (.of_forall fun x => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 n x)]
        by_cases hx : β n x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact (hfδ ((hs n x hx).trans hrn)).le) (h0 n x)
    _ = ε / 2 := by rw [integral_mul_const, h1 n, one_mul]
    _ < ε := half_lt_self hε

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem sum_norm_sq_eq (N : Matrix (Fin a) (Fin a) (Cinf E)) (w : InfinitePlace E) :
    ∑ i, ∑ j, ‖N i j w‖ ^ 2 = (Matrix.trace (star N * N) w).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

omit [NumberField E] [IsTotallyComplex E] in

theorem trace_star_mul_conj (k : Kinf E a) (N : Matrix (Fin a) (Fin a) (Cinf E)) :
    Matrix.trace (star ((k : Matrix (Fin a) (Fin a) (Cinf E)) * N * star (k : Matrix (Fin a) (Fin a) (Cinf E))) *
      ((k : Matrix (Fin a) (Fin a) (Cinf E)) * N * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) =
      Matrix.trace (star N * N) := by
  have h1 : star (k : Matrix (Fin a) (Fin a) (Cinf E)) * k = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set K : Matrix (Fin a) (Fin a) (Cinf E) := ↑k
  have e : star (K * N * star K) * (K * N * star K) = K * (star N * N * star K) := by
    rw [star_mul, star_mul, star_star]
    calc K * (star N * star K) * (K * N * star K) = K * star N * (star K * K) * N * star K := by
          simp only [mul_assoc]
      _ = K * (star N * N * star K) := by rw [h1, mul_one]; simp only [mul_assoc]
  rw [e, Matrix.trace_mul_comm, mul_assoc, h1, mul_one]

variable (E a) in

def frobSq (x : Lie E a) : ℝ := ∑ w, ∑ i, ∑ j, ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

omit [IsTotallyComplex E] in
theorem frobSq_eq (x : Lie E a) :
    frobSq E a x = ∑ w, ((Matrix.trace (star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      (Matrix.of x - 1)) : Cinf E) w).re := by
  rw [frobSq]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sum_norm_sq_eq]
  rfl

omit [IsTotallyComplex E] in

theorem frobSq_conj (k : Kinf E a) (x : Lie E a) :
    frobSq E a (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = frobSq E a x := by
  have h2 : (k : Matrix (Fin a) (Fin a) (Cinf E)) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  have e : Matrix.of (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) - 1 =
      (k : Matrix (Fin a) (Fin a) (Cinf E)) * (Matrix.of x - 1) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) := by
    rw [Unitary.coe_star, mul_sub, sub_mul, mul_one, h2]
    rfl
  rw [frobSq_eq, frobSq_eq, e, trace_star_mul_conj]

omit [IsTotallyComplex E] in
theorem contDiff_frobSq : ContDiff ℝ ∞ (frobSq E a) := by
  unfold frobSq
  refine ContDiff.sum fun w _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℝ).comp
    (((contDiff_apply ℝ ℂ w).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i))).sub contDiff_const)

omit [IsTotallyComplex E] in
theorem frobSq_one : frobSq E a (oneL E a) = 0 := by
  simp [frobSq]

omit [IsTotallyComplex E] in
theorem norm_sq_le_frobSq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖x i j w - oneL E a i j w‖ ^ 2 ≤ frobSq E a x := by
  unfold frobSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j,
    ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2) (fun w _ => by positivity) (Finset.mem_univ w))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j,
    ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ j)

variable (E a) in

def bumpR (m : ℝ) (x : Lie E a) : ℝ := Real.smoothTransition (1 - m ^ 2 * frobSq E a x)

omit [IsTotallyComplex E] in
theorem contDiff_bumpR (m : ℝ) : ContDiff ℝ ∞ (bumpR E a m) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_frobSq))

omit [IsTotallyComplex E] in
theorem bumpR_nonneg (m : ℝ) (x : Lie E a) : 0 ≤ bumpR E a m x := Real.smoothTransition.nonneg _

omit [IsTotallyComplex E] in
theorem bumpR_one (m : ℝ) : bumpR E a m (oneL E a) = 1 := by
  simp [bumpR, frobSq_one]

omit [IsTotallyComplex E] in
theorem dist_lt_of_bumpR_ne_zero {m : ℝ} (hm : 0 < m) {x : Lie E a} (h : bumpR E a m x ≠ 0) :
    dist x (oneL E a) < 1 / m := by
  have h1 : m ^ 2 * frobSq E a x < 1 := by
    by_contra hc
    exact h (Real.smoothTransition.zero_of_nonpos (by linarith))
  have hr : 0 < 1 / m := one_div_pos.2 hm
  rw [dist_pi_lt_iff hr]; intro i
  rw [dist_pi_lt_iff hr]; intro j
  rw [dist_pi_lt_iff hr]; intro w
  rw [Complex.dist_eq]
  have h2 := norm_sq_le_frobSq x i j w
  have h3 : (m * ‖x i j w - oneL E a i j w‖) ^ 2 < 1 := by
    rw [mul_pow]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
  have h4 : m * ‖x i j w - oneL E a i j w‖ < 1 := by
    have := abs_lt_of_sq_lt_sq' (h3.trans_eq (one_pow 2).symm) zero_le_one
    exact this.2
  rw [lt_div_iff₀ hm]
  linarith

omit [IsTotallyComplex E] in
theorem bumpR_conj (m : ℝ) (k : Kinf E a) (x : Lie E a) :
    bumpR E a m (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = bumpR E a m x := by
  simp only [bumpR, frobSq_conj]

end GlobalTheory.AutGrowth.ApproxId

namespace GlobalTheory.AutGrowth.ApproxId

theorem exists_approx_identity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure], ∃ α : ℕ → Lie E a → ℂ,
      (∀ n, IsTest (invSet E a) (α n) ∧ KInv (α n)) ∧
      ∀ ψ ∈ Sm E a, ∀ g, Tendsto (fun n => smoothing ν (α n) ψ g) atTop (𝓝 (ψ g)) := by
  intro E _ _ _ a ν _
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) (oneL E a) isUnit_one
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  let m : ℕ → ℝ := fun n => (n : ℝ) + N + 1
  have hm : ∀ n, 0 < m n := fun n => by positivity
  have hmN : ∀ n, 1 / m n < ε := fun n =>
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by simp [m])) hN
  have hsub : ∀ n, Metric.closedBall (oneL E a) (1 / m n) ⊆ invSet E a := fun n =>
    (Metric.closedBall_subset_ball (hmN n)).trans hball
  have hsupp : ∀ n, Function.support (bumpR E a (m n)) ⊆ Metric.closedBall (oneL E a) (1 / m n) :=
    fun n x hx => Metric.mem_closedBall.2 (dist_lt_of_bumpR_ne_zero (hm n) hx).le
  have hcs : ∀ n, HasCompactSupport (bumpR E a (m n)) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall (oneL E a) (1 / m n)) fun x hx => by
      by_contra h; exact hx (hsupp n h)
  have hpos : ∀ n, 0 < ∫ x, bumpR E a (m n) x ∂ν := fun n =>
    (contDiff_bumpR (m n)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs n)
      (fun x => bumpR_nonneg _ x) (x := oneL E a) (by rw [bumpR_one]; norm_num)
  let β : ℕ → Lie E a → ℝ := fun n x => (∫ y, bumpR E a (m n) y ∂ν)⁻¹ * bumpR E a (m n) x
  have hβs : ∀ n x, β n x ≠ 0 → dist x (oneL E a) < 1 / m n := fun n x h =>
    dist_lt_of_bumpR_ne_zero (hm n) (right_ne_zero_of_mul h)
  have hβc : ∀ n, ContDiff ℝ ∞ (β n) := fun n => contDiff_const.mul (contDiff_bumpR _)
  have hβcs : ∀ n, HasCompactSupport (β n) := fun n => (hcs n).mul_left
  have hT : ∀ n, IsTest (invSet E a) (fun x => (β n x : ℂ)) := fun n => by
    refine ⟨Complex.ofRealCLM.contDiff.comp (hβc n), ?_, ?_⟩
    · exact HasCompactSupport.intro (isCompact_closedBall (oneL E a) (1 / m n)) fun x hx => by
        by_contra h
        exact hx (Metric.mem_closedBall.2 (hβs n x (fun h' => h (by simp [h']))).le)
    · refine (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans (hsub n)
      exact Metric.mem_closedBall.2 (hβs n x (fun h' => hx (by simp [h']))).le
  refine ⟨fun n x => (β n x : ℂ), fun n => ⟨hT n, fun k x => ?_⟩, fun ψ hψ g => ?_⟩
  · simp only [β, bumpR_conj]
  · have hv : chart ψ g (oneL E a) = ψ g := by
      have := chart_val ψ g 1
      simpa using this
    have hf : ContinuousAt (chart ψ g) (oneL E a) := (contDiffAt_chart hψ g isUnit_one).continuousAt
    have hr : Tendsto (fun n => 1 / m n) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (one_div_pos.2 (hm n)).le) (fun n => ?_)
      exact one_div_le_one_div_of_le (by positivity) (by simp [m])
    have h1 : ∀ n, ∫ x, β n x ∂ν = 1 := fun n => by
      simp only [β]
      rw [integral_const_mul, inv_mul_cancel₀ (hpos n).ne']
    have key := tendsto_integral_of_concentrate hf β (fun n => 1 / m n) hr
      (fun n x => mul_nonneg (inv_nonneg.2 (hpos n).le) (bumpR_nonneg _ x)) h1 hβs
      (fun n => (hβc n).continuous.integrable_of_hasCompactSupport (hβcs n))
      (fun n => (hT n).integrable_mul ν isOpen_invSet (hψ g).continuousOn)
    rw [hv] at key
    exact key

end GlobalTheory.AutGrowth.ApproxId
