import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt

open Filter Topology

namespace GlobalTheory.ConjSeries

section General

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem hasDerivAt_prod_pow_line (α : σ →₀ ℕ) (z : σ → ℂ) (i : σ) :
    HasDerivAt (fun t : ℂ => ∏ j, (z + t • (Pi.single i 1 : σ → ℂ)) j ^ α j)
      ((α i : ℂ) * z i ^ (α i - 1) * ∏ j ∈ Finset.univ.erase i, z j ^ α j) 0 := by
  have h : (fun t : ℂ => ∏ j, (z + t • (Pi.single i 1 : σ → ℂ)) j ^ α j) =
      fun t : ℂ => (z i + t) ^ α i * ∏ j ∈ Finset.univ.erase i, z j ^ α j := by
    funext t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun j hj => ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h]
  have h2 := (((hasDerivAt_id (0 : ℂ)).const_add (z i)).fun_pow (α i)).mul_const
    (∏ j ∈ Finset.univ.erase i, z j ^ α j)
  simpa using h2

theorem hasSum_fderiv_series {f : (σ → ℂ) → ℂ} {c : (σ →₀ ℕ) → ℂ} (hf : AnalyticAt ℂ f 0)
    (h : ∀ᶠ z in 𝓝 (0 : σ → ℂ), HasSum (fun α : σ →₀ ℕ => c α * ∏ j, z j ^ α j) (f z)) (i : σ) :
    ∀ᶠ z in 𝓝 (0 : σ → ℂ), HasSum (fun α : σ →₀ ℕ =>
      (c (α + Finsupp.single i 1) * ((α i : ℂ) + 1)) * ∏ j, z j ^ α j)
      (fderiv ℂ f z (Pi.single i 1)) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 h
  set s : ℝ := r / 2 with hs
  have hs0 : 0 < s := by positivity
  have hsum : Summable fun α : σ →₀ ℕ => ‖c α‖ * ∏ j, s ^ α j := by
    have h1 := (hball (fun _ => (s : ℂ)) (by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
      intro j
      rw [Complex.norm_real, Real.norm_of_nonneg hs0.le]; linarith)).summable.norm
    simpa [norm_prod, abs_of_pos hs0] using h1
  filter_upwards [hf.eventually_analyticAt, Metric.ball_mem_nhds (0 : σ → ℂ) (half_pos hs0)]
    with z hz hzb
  rw [mem_ball_zero_iff] at hzb
  have hn : ∀ t ∈ Metric.ball (0 : ℂ) (s / 2), ‖z + t • (Pi.single i 1 : σ → ℂ)‖ < s := by
    intro t ht
    rw [mem_ball_zero_iff] at ht
    calc _ ≤ ‖z‖ + ‖t • (Pi.single i 1 : σ → ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + ‖t‖ := by rw [norm_smul, Pi.norm_single, norm_one, mul_one]
      _ < s := by linarith
  have h1 := Complex.hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) (s / 2))
    (F := fun (α : σ →₀ ℕ) (t : ℂ) => c α * ∏ j, (z + t • (Pi.single i 1 : σ → ℂ)) j ^ α j)
    hsum (fun α => by
      apply Differentiable.differentiableOn
      simp only [Pi.add_apply, Pi.smul_apply]
      fun_prop) Metric.isOpen_ball (fun α t ht => by
      rw [norm_mul, norm_prod]
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_)
        (norm_nonneg _)
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm _ j).trans (hn t ht).le) _)
    (Metric.mem_ball_self (half_pos hs0))
  have h2 : (fun t : ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, (z + t • (Pi.single i 1 : σ → ℂ)) j ^ α j)
      =ᶠ[𝓝 0] fun t : ℂ => f (z + t • (Pi.single i 1 : σ → ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (half_pos hs0)] with t ht
    exact (hball _ (by rw [mem_ball_zero_iff]; linarith [hn t ht])).tsum_eq
  rw [h2.deriv_eq] at h1
  have h3 : deriv (fun t : ℂ => f (z + t • (Pi.single i 1 : σ → ℂ))) 0 =
      fderiv ℂ f z (Pi.single i 1) := hz.differentiableAt.lineDeriv_eq_fderiv
  rw [h3] at h1
  have h5 : HasSum (fun α : σ →₀ ℕ => c α *
      ((α i : ℂ) * z i ^ (α i - 1) * ∏ j ∈ Finset.univ.erase i, z j ^ α j))
      (fderiv ℂ f z (Pi.single i 1)) := by
    refine (congrArg (HasSum · _) (funext fun α => ?_)).mp h1
    exact ((hasDerivAt_prod_pow_line α z i).const_mul (c α)).deriv
  have hinj : Function.Injective fun α : σ →₀ ℕ => α + Finsupp.single i 1 :=
    add_left_injective _
  rw [← hinj.hasSum_iff] at h5
  · convert h5 using 2 with α
    simp only [Function.comp]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have : ∏ j ∈ Finset.univ.erase i, z j ^ (α + Finsupp.single i 1 : σ →₀ ℕ) j =
        ∏ j ∈ Finset.univ.erase i, z j ^ α j :=
      Finset.prod_congr rfl fun j hj => by
        simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this]
    simp
    ring
  · intro α hα
    have : α i = 0 := by
      by_contra h0
      have hle : Finsupp.single i 1 ≤ α := by
        rw [Finsupp.single_le_iff]; omega
      obtain ⟨m', rfl⟩ := exists_add_of_le hle
      exact hα ⟨m', add_comm _ _⟩
    simp [this]

theorem coeff_taylor_of_hasSum (n : ℕ) :
    ∀ {f : (σ → ℂ) → ℂ} {c : (σ →₀ ℕ) → ℂ}, AnalyticAt ℂ f 0 →
    (∀ᶠ z in 𝓝 (0 : σ → ℂ), HasSum (fun α : σ →₀ ℕ => c α * ∏ j, z j ^ α j) (f z)) →
    ∀ m : σ →₀ ℕ, m.degree < n → MvPowerSeries.coeff m (GlobalTheory.taylor f) = c m := by
  induction n with
  | zero => intro f c _ _ m hm; omega
  | succ n ih =>
    intro f c hf h m hm
    by_cases h0 : m = 0
    · subst h0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_taylor]
      have h1 := h.self_of_nhds
      have h2 : HasSum (fun α : σ →₀ ℕ => c α * ∏ j, (0 : σ → ℂ) j ^ α j)
          (c 0 * ∏ j, (0 : σ → ℂ) j ^ (0 : σ →₀ ℕ) j) := by
        refine hasSum_single 0 fun α hα => ?_
        obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by simpa using Finsupp.ne_iff.1 hα
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
      simpa using h1.unique h2
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h0
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨m', rfl⟩ := exists_add_of_le hle
    have h1 := ih (analyticAt_fderiv_apply hf (Pi.single i 1)) (hasSum_fderiv_series hf h i) m' (by
      rw [map_add, Finsupp.degree_single] at hm; omega)
    rw [taylor_fderiv hf, MvPowerSeries.coeff_pderiv] at h1
    have h4 : ((m' i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' i)
    rw [add_comm]
    exact mul_right_cancel₀ h4 h1

omit [DecidableEq σ] in

theorem eventually_summable_of_ne_zero {c : (σ →₀ ℕ) → ℂ}
    (hf : Continuous fun z : σ → ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, z j ^ α j)
    (h0 : (fun z : σ → ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, z j ^ α j) ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : σ → ℂ), Summable (fun α : σ →₀ ℕ => c α * ∏ j, z j ^ α j) := by
  have hd : Dense (Set.pi Set.univ fun _ : σ => ({0}ᶜ : Set ℂ)) :=
    dense_pi Set.univ fun _ _ => dense_compl_singleton 0
  obtain ⟨w, hw, hw0⟩ := hd.inter_open_nonempty _ (isOpen_ne_fun hf continuous_zero)
    (Function.ne_iff.1 h0)
  have hs : Summable (fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j) := by
    by_contra hs
    exact hw (tsum_eq_zero_of_not_summable hs)
  have hev : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ∀ j, ‖z j‖ < ‖w j‖ := by
    refine eventually_all.2 fun j => ?_
    refine (continuous_apply j).norm.continuousAt.eventually_lt continuousAt_const ?_
    simpa using hw0 j (Set.mem_univ j)
  filter_upwards [hev] with z hz
  refine Summable.of_norm_bounded hs.norm fun α => ?_
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_)
    (norm_nonneg _)
  rw [norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hz j).le _

end General

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem taylor_eq_coeff (D : D7) {N N' : ℕ} (F : VC D N N' → ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D F α = MvPowerSeries.coeff α (taylorDir (coordV D) F) := by
  rw [coeff_taylorDir, dirPolyDeriv_monomial_one, Formalism.MainNotions.TaylorLogMetric.taylor,
    Finsupp.prod_fintype _ _ (by simp), Nat.cast_prod, div_eq_inv_mul]
  rfl

theorem taylor_tsum (D : D7) {N N' : ℕ} (c : Mono D N N' → ℂ)
    (hd : Differentiable ℂ fun z : VC D N N' => ∑' α, c α * mono D α z)
    (h0 : (fun z : VC D N N' => ∑' α, c α * mono D α z) ≠ 0) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z : VC D N N' => ∑' α, c α * mono D α z) α = c α := by
  let L : (D.what₂.Tau × Fin N' × Fin N → ℂ) →L[ℂ] VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      ContinuousLinearMap.proj (τ, a, b)
  have hL : ∀ z τ a b, L z τ a b = z (τ, a, b) := fun _ _ _ _ => rfl
  have hc : coordV D = fun k => L (Pi.single k 1) := by
    funext ⟨k1, k2, k3⟩ τ a b
    simp [hL, coordV, Pi.single_apply]
  have hm : ∀ (β : Mono D N N') z, mono D β (L z) = ∏ j, z j ^ β j := fun β z => by
    rw [mono, Finsupp.prod_fintype _ _ (by simp)]
    rfl
  have han : AnalyticAt ℂ (fun z : VC D N N' => ∑' α, c α * mono D α z) 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Eventually.of_forall hd)
  rw [taylor_eq_coeff, hc, ← taylor_comp_clm L han]
  have han' : AnalyticAt ℂ (fun z => ∑' α, c α * mono D α (L z)) 0 :=
    han.comp_of_eq (L.analyticAt 0) (map_zero L)
  have hcont : Continuous (fun z => ∑' α, c α * mono D α (L z)) :=
    hd.continuous.comp L.continuous
  have hne : (fun z => ∑' α, c α * mono D α (L z)) ≠ 0 := by
    intro h
    refine h0 (funext fun w => ?_)
    exact congrFun h fun k => w k.1 k.2.1 k.2.2
  simp only [hm] at han' hcont hne ⊢
  refine coeff_taylor_of_hasSum _ han' ?_ α (Nat.lt_succ_self _)
  filter_upwards [eventually_summable_of_ne_zero hcont hne] with z hz
  exact hz.hasSum

theorem coeff_minorPol_int (D : D7) {N N' : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D N N' n)
    (α : Mono D N N') : ∃ k : ℤ, MvPolynomial.coeff α (minorPol D T) = k := by
  have h : minorPol D T = MvPolynomial.map (Int.castRingHom ℂ)
      (∏ τ, ∏ j, (Matrix.of fun i i' : Fin N =>
        (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D N N') ℤ)).det) := by
    simp only [minorPol, map_prod, RingHom.map_det]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
    congr 1
    ext i i' : 2
    simp
  exact ⟨_, by rw [h, MvPolynomial.coeff_map]; rfl⟩

theorem taylor_fnConj : ∀ (D : D7) (N N' : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D N N' → ℂ), Differentiable ℂ (fnConj D M ρ G) → fnConj D M ρ G ≠ 0 → (∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (fnConj D M ρ G) α = cj M ρ (Formalism.MainNotions.TaylorLogMetric.taylor D G α)) ∧ (CoefIn D G M → ∀ (n : D.what₂.Tau → ℕ) (T : Tup D N N' n), GL3Theta.applyAt0 D (minorPol D T) G ∈ M ∧ cj M ρ (GL3Theta.applyAt0 D (minorPol D T) G) = GL3Theta.applyAt0 D (minorPol D T) (fnConj D M ρ G)) := by
  intro D N N' M ρ G hd h0
  have h1 : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (fnConj D M ρ G) α = cj M ρ (Formalism.MainNotions.TaylorLogMetric.taylor D G α) :=
    fun α => taylor_tsum D _ hd h0 α
  refine ⟨h1, fun hG n T => ?_⟩
  choose k hk using coeff_minorPol_int D T
  have hcj : ∀ x : M, cj M ρ x = ρ x := fun x => by simp [cj, TaylorLogMetric.liftM]
  let x : M := ∑ α ∈ (minorPol D T).support,
    (k α : M) * ((α.prod fun _ n => n.factorial : ℕ) : M) * ⟨_, hG α⟩
  have hx : GL3Theta.applyAt0 D (minorPol D T) G = x := by
    simp [GL3Theta.applyAt0, x, hk, Finsupp.prod]
  rw [hx, hcj]
  refine ⟨x.2, ?_⟩
  simp only [GL3Theta.applyAt0, x, hk, h1, map_sum, map_mul, map_intCast, map_natCast]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← hcj]
  simp [Finsupp.prod]

end GlobalTheory.ConjSeries
