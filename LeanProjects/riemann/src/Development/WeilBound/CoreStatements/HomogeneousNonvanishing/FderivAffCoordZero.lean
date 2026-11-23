import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.FsMetricFinIsSemipositive
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

namespace GP

open ReciprocityTheory.AnForm

theorem levi_sum {κ : Type} [Fintype κ] {K : Type} (s : Finset K) (f : K → (κ → ℂ) → ℝ) (z w : κ → ℂ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) : levi (fun y => ∑ k ∈ s, f k y) z w = ∑ k ∈ s, levi (f k) z w := by
  have hd : ∀ k, ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ (f k) y := fun k =>
    ((hf k).eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hd2 : ∀ k, DifferentiableAt ℝ (fderiv ℝ (f k)) z := fun k =>
    ((hf k).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEq : fderiv ℝ (fun y => ∑ k ∈ s, f k y) =ᶠ[𝓝 z] fun y => ∑ k ∈ s, fderiv ℝ (f k) y := by
    filter_upwards [(Filter.eventually_all_finset s).2 (fun k _ => hd k)] with y hy
    have h1 := fderiv_sum hy
    rwa [show (∑ i ∈ s, f i) = fun y => ∑ k ∈ s, f k y from by ext; simp] at h1
  have h2 := fderiv_sum (fun k (_ : k ∈ s) => hd2 k)
  rw [show (∑ i ∈ s, fderiv ℝ (f i)) = fun y => ∑ k ∈ s, fderiv ℝ (f k) y from by ext; simp] at h2
  unfold levi
  rw [hEq.fderiv_eq, h2]
  simp only [ContinuousLinearMap.sum_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_div]

theorem levi_fs_nonneg {κ : Type} [Fintype κ] {z : κ → ℂ} (hz : z ≠ 0) (w : κ → ℂ) :
    0 ≤ levi (fun z => Real.log ((fsMetric κ).ρ z)) z w := fsMetric_isSemipositive.2 z hz w

private theorem fderiv_fderiv_eq_deriv_deriv_line {κ : Type} [Fintype κ] {φ : (κ → ℂ) → ℝ} {z : κ → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (v : κ → ℂ) :
    fderiv ℝ (fderiv ℝ φ) z v v = deriv (deriv (fun t : ℝ => φ (z + t • v))) 0 := by
  have hd : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  have hlim : Filter.Tendsto (fun s : ℝ => z + s • v) (𝓝 0) (𝓝 z) := by
    simpa using (hγ 0).continuousAt.tendsto
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ φ (z + t • v) := hlim.eventually hd
  have h1 : deriv (fun t : ℝ => φ (z + t • v)) =ᶠ[𝓝 0] fun t => fderiv ℝ φ (z + t • v) v := by
    filter_upwards [hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  rw [h1.deriv_eq]
  have h2 : HasFDerivAt (fun y => fderiv ℝ φ y v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ φ) z)) z :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z hd2.hasFDerivAt
  have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ φ (z + t • v) v) (fderiv ℝ (fderiv ℝ φ) z v v) 0 :=
    h2.comp_hasDerivAt_of_eq (0 : ℝ) (hγ 0) (by simp)
  exact h3.deriv.symm

private theorem deriv_deriv_half_log_quadratic_at_zero (N P C : ℝ) (hN : 0 < N) :
    deriv (deriv (fun t : ℝ => Real.log (N + 2 * t * P + t ^ 2 * C) / 2)) 0 =
      (C * N - 2 * P ^ 2) / N ^ 2 := by
  have hN' : N ≠ 0 := hN.ne'
  have hq : ∀ t : ℝ, HasDerivAt (fun s : ℝ => N + 2 * s * P + s ^ 2 * C) (2 * P + 2 * t * C) t := by
    intro t
    have h1 := ((hasDerivAt_id' t).const_mul (2 * P)).const_add N
    have h2 := (hasDerivAt_pow 2 t).mul_const C
    have e : (fun s : ℝ => N + 2 * s * P + s ^ 2 * C) = (fun x => N + 2 * P * x) + (fun y => y ^ 2 * C) := by
      funext s
      simp only [Pi.add_apply]
      ring
    rw [e]
    exact (h1.add h2).congr_deriv (by
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring)
  have hq0 : N + 2 * (0 : ℝ) * P + (0 : ℝ) ^ 2 * C ≠ 0 := by simpa using hN'
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), N + 2 * t * P + t ^ 2 * C ≠ 0 :=
    (hq 0).continuousAt.eventually_ne hq0
  have hd : deriv (fun t : ℝ => Real.log (N + 2 * t * P + t ^ 2 * C) / 2) =ᶠ[𝓝 0]
      fun t => (P + C * t) / (N + 2 * t * P + t ^ 2 * C) := by
    filter_upwards [hev] with t ht
    rw [(((hq t).log ht).div_const 2).deriv]
    field_simp <;> ring
  rw [hd.deriv_eq]
  have h4 := (((hasDerivAt_id' (0 : ℝ)).const_mul C).const_add P).div (hq 0) hq0
  rw [show (fun t : ℝ => (P + C * t) / (N + 2 * t * P + t ^ 2 * C)) =
    (fun x => P + C * x) / (fun s => N + 2 * s * P + s ^ 2 * C) from rfl, h4.deriv]
  simp only [mul_zero, zero_mul, add_zero, mul_one, zero_pow two_ne_zero]
  field_simp <;> ring

theorem levi_fs_zero {κ : Type} [Fintype κ] {z : κ → ℂ} (hz : z ≠ 0) (w : κ → ℂ)
    (h : levi (fun z => Real.log ((fsMetric κ).ρ z)) z w = 0) : ∃ c : ℂ, w = c • z := by
  have hxne : WithLp.toLp 2 z ≠ 0 := fun h => hz (by simpa using congrArg WithLp.ofLp h)
  have hN : 0 < ‖WithLp.toLp 2 z‖ ^ 2 := pow_pos (norm_pos_iff.2 hxne) 2
  have hρ : ContDiffAt ℝ 2 (fun u : κ → ℂ => (fsMetric κ).ρ u) z := by
    show ContDiffAt ℝ 2 (fun u => ‖WithLp.toLp 2 u‖) z
    exact (contDiffAt_norm ℂ hxne).comp z
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.contDiff.contDiffAt)
  have hφ : ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric κ).ρ u)) z :=
    hρ.log (ne_of_gt ((fsMetric κ).pos z hz))
  have key : ∀ v : κ → ℂ, fderiv ℝ (fderiv ℝ (fun u => Real.log ((fsMetric κ).ρ u))) z v v =
      (‖WithLp.toLp 2 v‖ ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 -
        2 * (inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 v)).re ^ 2) / (‖WithLp.toLp 2 z‖ ^ 2) ^ 2 := by
    intro v
    rw [fderiv_fderiv_eq_deriv_deriv_line hφ v]
    have hF : (fun t : ℝ => Real.log ((fsMetric κ).ρ (z + t • v))) = fun t : ℝ =>
        Real.log (‖WithLp.toLp 2 z‖ ^ 2 + 2 * t * (inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 v)).re +
          t ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2) / 2 := by
      funext t
      have e : WithLp.toLp 2 (z + t • v) = WithLp.toLp 2 z + (t : ℂ) • WithLp.toLp 2 v := by
        rw [WithLp.toLp_add, WithLp.toLp_smul, Complex.coe_smul]
      show Real.log ‖WithLp.toLp 2 (z + t • v)‖ = _
      have hsq : ‖WithLp.toLp 2 z + (t : ℂ) • WithLp.toLp 2 v‖ ^ 2 =
          ‖WithLp.toLp 2 z‖ ^ 2 + 2 * t * (inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 v)).re +
            t ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, RCLike.re_to_complex, Complex.re_ofReal_mul,
          norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        ring
      rw [e, ← hsq, Real.log_pow]
      push_cast
      ring
    rw [hF, deriv_deriv_half_log_quadratic_at_zero _ _ _ hN]
  have hI : inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 (Complex.I • w)) =
      Complex.I * inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 w) := by
    rw [WithLp.toLp_smul, inner_smul_right]
  have hIn : ‖WithLp.toLp 2 (Complex.I • w)‖ = ‖WithLp.toLp 2 w‖ := by
    rw [WithLp.toLp_smul, norm_smul]
    simp
  unfold levi at h
  rw [key, key, hI, hIn, Complex.I_mul_re, neg_sq] at h
  rw [← add_div, div_div, div_eq_zero_iff] at h
  have hsum : ‖WithLp.toLp 2 w‖ ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 =
      (inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 w)).re ^ 2 +
        (inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 w)).im ^ 2 := by
    rcases h with h | h
    · linarith
    · exfalso
      have : 0 < (‖WithLp.toLp 2 z‖ ^ 2) ^ 2 * 4 := by positivity
      linarith
  have hcs : ‖inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 w)‖ = ‖WithLp.toLp 2 z‖ * ‖WithLp.toLp 2 w‖ := by
    have hsq : ‖inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 w)‖ ^ 2 =
        (‖WithLp.toLp 2 z‖ * ‖WithLp.toLp 2 w‖) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow]
      linear_combination -hsum
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  by_cases hw : WithLp.toLp 2 w = 0
  · refine ⟨0, ?_⟩
    simpa using congrArg WithLp.ofLp hw
  · obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hxne hw).1 hcs
    refine ⟨r, ?_⟩
    have := congrArg WithLp.ofLp hr
    simpa using this

theorem contDiffAt_fs {κ : Type} [Fintype κ] {z : κ → ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fsMetric κ).ρ z :=
  ContDiffOn.contDiffAt fsMetric_isSmooth (isOpen_ne.mem_nhds hz)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def blk (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj ⟨k, i⟩

theorem blk_ne {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) : blk k z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz k
  intro h
  apply hi
  have := congrFun h i
  simpa [blk] using this

theorem fderiv_affCoord_zero (p : (k : K) → ι k) {z v : (Σ k, ι k) → ℂ} (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) (c : K → ℂ)
    (hv : ∀ q, v q = c q.1 * z q) : fderiv ℂ (affCoord p) z v = 0 := by
  have hl : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have h1 := HasFDerivAt.comp_hasDerivAt_of_eq 0 (HolomorphicMinorCharts.analyticAt_affCoord p hz).differentiableAt.hasFDerivAt hl
    (by simp)
  have h2 : HasDerivAt (affCoord p ∘ fun t : ℂ => z + t • v) 0 0 := by
    refine (hasDerivAt_const (0 : ℂ) (affCoord p z)).congr_of_eventuallyEq ?_
    have : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ k, 1 + t * c k ≠ 0 := eventually_all.mpr fun k =>
      ContinuousAt.eventually_ne (by fun_prop) (by simp)
    filter_upwards [this] with t ht
    refine HolomorphicMinorCharts.affCoord_so ⟨fun k => 1 + t * c k, ht, funext fun q => ?_⟩ p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv q]
    ring
  exact h1.unique h2

end GP

private theorem contDiffAt_fsMetric_rho_blk {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (k : K)
    {z : (k : K) × ι k → ℂ} (hz : GP.blk k z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (k : K) × ι k → ℂ => (fsMetric (ι k)).ρ (GP.blk k z)) z := by
  have h1 : WithLp.toLp 2 (GP.blk k z) ≠ 0 := fun h => hz (by simpa using congrArg WithLp.ofLp h)
  show ContDiffAt ℝ _ (fun z => ‖WithLp.toLp 2 (GP.blk k z)‖) z
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (k : K) × ι k → ℂ => WithLp.toLp 2 (GP.blk k z)) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι k => ℂ)).symm.toContinuousLinearMap.comp
      ((GP.blk k).restrictScalars ℝ)).contDiff
  exact (contDiffAt_norm ℂ h1).comp z hL.contDiffAt

private theorem contDiffAt_log_fsMetric_rho {κ : Type} [Fintype κ] {z : κ → ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : κ → ℂ => Real.log ((fsMetric κ).ρ v)) z := by
  have h1 : WithLp.toLp 2 z ≠ 0 := fun h => hz (by simpa using congrArg WithLp.ofLp h)
  have hρ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : κ → ℂ => (fsMetric κ).ρ u) z := by
    show ContDiffAt ℝ _ (fun u => ‖WithLp.toLp 2 u‖) z
    exact (contDiffAt_norm ℂ h1).comp z
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.contDiff.contDiffAt)
  exact hρ.log (ne_of_gt ((fsMetric κ).pos z hz))

private theorem contDiffAt_log_prod_fsMetric_rho_blk {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (k : K) × ι k → ℂ} (hz : ∀ k, GP.blk k z ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (k : K) × ι k → ℂ => Real.log (∏ k, (fsMetric (ι k)).ρ (GP.blk k z))) z := by
  have hpos : 0 < ∏ k, (fsMetric (ι k)).ρ (GP.blk k z) :=
    Finset.prod_pos fun k _ => (fsMetric _).pos _ (hz k)
  exact (contDiffAt_prod fun k _ => contDiffAt_fsMetric_rho_blk k (hz k)).log hpos.ne'

private theorem levi_log_prod_fsMetric_eq_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (k : K) × ι k → ℂ} (hz : ∀ k, GP.blk k z ≠ 0) (u : (k : K) × ι k → ℂ) :
    ReciprocityTheory.AnForm.levi (fun z : (k : K) × ι k → ℂ => Real.log (∏ k, (fsMetric (ι k)).ρ (GP.blk k z))) z u =
      ∑ k, ReciprocityTheory.AnForm.levi (fun v : ι k → ℂ => Real.log ((fsMetric (ι k)).ρ v)) (GP.blk k z) (GP.blk k u) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have hev : ∀ᶠ y in 𝓝 z, ∀ k, GP.blk k y ≠ 0 := by
    rw [Filter.eventually_all]
    intro k
    exact (GP.blk k).continuous.continuousAt.eventually_ne (hz k)
  have hcongr : (fun z : (k : K) × ι k → ℂ => Real.log (∏ k, (fsMetric (ι k)).ρ (GP.blk k z))) =ᶠ[𝓝 z]
      fun y => ∑ k ∈ Finset.univ, Real.log ((fsMetric (ι k)).ρ (GP.blk k y)) := by
    filter_upwards [hev] with y hy
    exact Real.log_prod (fun k _ => ((fsMetric _).pos _ (hy k)).ne')
  rw [ReciprocityTheory.AnForm.levi_congr hcongr]
  rw [GP.levi_sum (f := fun k y => Real.log ((fsMetric (ι k)).ρ (GP.blk k y)))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hc := ReciprocityTheory.AnForm.levi_comp (φ := fun v : ι k → ℂ => Real.log ((fsMetric (ι k)).ρ v))
      (τ := GP.blk (ι := ι) k) u ((GP.blk (ι := ι) k).analyticAt z) ((contDiffAt_log_fsMetric_rho (hz k)).of_le h2)
    rw [ContinuousLinearMap.fderiv] at hc
    exact hc
  · intro k
    exact (((contDiffAt_log_fsMetric_rho (hz k)).comp z
      (((GP.blk (ι := ι) k).contDiff.contDiffAt).restrict_scalars ℝ)).of_le h2)

private theorem exists_holo_re_eq_sub_of_log_scaling {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type}
    [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X}
    {lam : X → X → (k : K) × ι k → ℂ} (emb : IsEmbedded A P U lam) (Φ : ((k : K) × ι k → ℂ) → ℝ)
    (hΦ : ∀ (c : K → ℂ) (z : (k : K) × ι k → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      Φ (fun p => c p.1 * z p) = ∑ k, Real.log ‖c k‖ + Φ z)
    (x x' y : X) (hy : y ∈ U x ∩ U x') :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W ∩ U x ∩ U x', Φ (lam x z) - Φ (lam x' z) = (G z).re := by
  have hm : lam x' y ∈ mcPts P := emb.mem x' y hy.2
  choose q hq using hm.1
  have hq' : ∀ k, lam x y ⟨k, q k⟩ ≠ 0 := fun k =>
    (HolomorphicMinorCharts.ne_zero_so (emb.compat x x' y hy) _).2 (hq k)
  have hc0 : ∀ k, lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩ ≠ 0 := fun k => div_ne_zero (hq' k) (hq k)
  have hcont : ∀ x'' p, y ∈ U x'' → ContinuousAt (fun z => lam x'' z p) y := fun _ p h =>
    HolomorphicMinorCharts.holo_continuousAt (emb.holo _ p) h
  have hev : ∀ᶠ z in 𝓝 y, z ∈ U x ∧ z ∈ U x' ∧ ∀ k, lam x' z ⟨k, q k⟩ ≠ 0 ∧
      lam x z ⟨k, q k⟩ / lam x' z ⟨k, q k⟩ / (lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩) ∈ Complex.slitPlane := by
    refine Filter.Eventually.and ((emb.isOpen x).mem_nhds hy.1)
      (Filter.Eventually.and ((emb.isOpen x').mem_nhds hy.2) ?_)
    rw [Filter.eventually_all]
    intro k
    have h1 := (hcont x' ⟨k, q k⟩ hy.2).eventually_ne (hq k)
    have h2 : ContinuousAt (fun z => lam x z ⟨k, q k⟩ / lam x' z ⟨k, q k⟩ /
        (lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩)) y :=
      ((hcont x _ hy.1).div (hcont x' _ hy.2) (hq k)).div_const _
    have h3 : lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩ / (lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩) ∈
        Complex.slitPlane := by
      rw [div_self (hc0 k)]
      exact Complex.one_mem_slitPlane
    exact h1.and (h2.eventually_mem (Complex.isOpen_slitPlane.mem_nhds h3))
  obtain ⟨W, hWP, hWo, hyW⟩ := eventually_nhds_iff.1 hev
  refine ⟨W, hWo, hyW, fun z => ∑ k, (Complex.log (lam x z ⟨k, q k⟩ / lam x' z ⟨k, q k⟩ /
      (lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩)) + ((Real.log ‖lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩‖ : ℝ) : ℂ)),
    ?_, ?_⟩
  · intro j v hv
    obtain ⟨hvt, hvW⟩ := hv
    have hP := hWP _ hvW
    have ha : ∀ x'' p, (A.chart j).symm v ∈ U x'' →
        AnalyticAt ℂ ((fun z => lam x'' z p) ∘ (A.chart j).symm) v := fun x'' p h =>
      emb.holo x'' p j v ⟨hvt, h⟩
    show AnalyticAt ℂ (fun v => ∑ k, (Complex.log (lam x ((A.chart j).symm v) ⟨k, q k⟩ /
      lam x' ((A.chart j).symm v) ⟨k, q k⟩ / (lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩)) +
        ((Real.log ‖lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩‖ : ℝ) : ℂ))) v
    apply Finset.analyticAt_fun_sum
    intro k _
    apply AnalyticAt.add _ analyticAt_const
    have hf : AnalyticAt ℂ (fun a => lam x ((A.chart j).symm a) ⟨k, q k⟩ /
        lam x' ((A.chart j).symm a) ⟨k, q k⟩ / (lam x y ⟨k, q k⟩ / lam x' y ⟨k, q k⟩)) v :=
      ((ha x _ hP.1).div (ha x' _ hP.2.1) (hP.2.2 k).1).div analyticAt_const (hc0 k)
    exact hf.clog (hP.2.2 k).2
  · rintro z ⟨⟨hzW, hzx⟩, hzx'⟩
    obtain ⟨c, hc, hceq⟩ := emb.compat x x' z ⟨hzx, hzx'⟩
    have hΦz : Φ (lam x z) = ∑ k, Real.log ‖c k‖ + Φ (lam x' z) := by
      rw [hceq]
      exact hΦ c _ hc (emb.mem x' z hzx').1
    rw [hΦz, add_sub_cancel_right, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hb := ((hWP z hzW).2.2 k).1
    have hk : lam x z ⟨k, q k⟩ = c k * lam x' z ⟨k, q k⟩ := by rw [hceq]
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re]
    rw [hk, mul_div_cancel_right₀ _ hb, norm_div (c k),
      Real.log_div (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hc0 k))]
    ring

private theorem log_prod_fsMetric_blk_smul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (c : K → ℂ) (z : (k : K) × ι k → ℂ) (hc : ∀ k, c k ≠ 0) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (∏ k, (fsMetric (ι k)).ρ (GP.blk k (fun p => c p.1 * z p))) =
      ∑ k, Real.log ‖c k‖ + Real.log (∏ k, (fsMetric (ι k)).ρ (GP.blk k z)) := by
  have hb : ∀ k, GP.blk k (fun p : (k : K) × ι k => c p.1 * z p) = c k • GP.blk k z := by
    intro k
    ext i
    simp [GP.blk]
  simp only [hb, (fsMetric _).smul]
  rw [Finset.prod_mul_distrib, Real.log_mul, Real.log_prod]
  · exact fun k _ => norm_ne_zero_iff.2 (hc k)
  · exact Finset.prod_ne_zero_iff.2 fun k _ => norm_ne_zero_iff.2 (hc k)
  · exact (Finset.prod_pos fun k _ => (fsMetric _).pos _ (GP.blk_ne hz k)).ne'

open GP HolomorphicMinorCharts ReciprocityTheory.AnForm in
theorem g_pos : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsEmbedded R.A P R.U R.lift → ∃ Amp : HermLine ι, IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) := by
  intro K _ ι _ P J e R emb
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have hsm : ∀ (c : K → ℂ) (z : (k : K) × ι k → ℂ), (∀ k, c k ≠ 0) →
      (∏ k, (fsMetric (ι k)).ρ (blk k (fun p : (k : K) × ι k => c p.1 * z p))) =
        (∏ k, ‖c k‖ ^ (1 : ℤ)) * ∏ k, (fsMetric (ι k)).ρ (blk k z) := by
    intro c z hc
    have hb : ∀ k, blk k (fun p : (k : K) × ι k => c p.1 * z p) = c k • blk k z := by
      intro k
      ext i
      simp [blk]
    simp only [hb, (fsMetric _).smul, zpow_one]
    exact Finset.prod_mul_distrib
  have hpos : ∀ z : (k : K) × ι k → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      0 < ∏ k, (fsMetric (ι k)).ρ (blk k z) := fun z hz =>
    Finset.prod_pos fun k _ => (fsMetric _).pos _ (blk_ne hz k)
  let Amp : HermLine ι := ⟨fun _ => 1, fun z => ∏ k, (fsMetric (ι k)).ρ (blk k z), hpos, hsm⟩
  have hΦ := fun c z hc hz => log_prod_fsMetric_blk_smul (ι := ι) c z hc hz
  refine ⟨Amp, ?_, ?_, ?_⟩
  · intro z hz
    exact (contDiffAt_prod fun k _ => contDiffAt_fsMetric_rho_blk k (blk_ne hz k)).contDiffWithinAt
  · refine ⟨fun x j v hv => ?_, fun x x' y hy => ?_⟩
    · apply ContDiffAt.contDiffWithinAt
      have hτ : AnalyticAt ℂ (fun u => R.lift x ((R.A.chart j).symm u)) v :=
        AnalyticAt.pi (fun p => emb.holo x p j v hv)
      have hm := emb.mem x _ hv.2
      have := (contDiffAt_log_prod_fsMetric_rho_blk (fun k => blk_ne hm.1 k)).comp v (hτ.contDiffAt.restrict_scalars ℝ)
      exact this
    · exact exists_holo_re_eq_sub_of_log_scaling emb (fun z => Real.log (∏ k, (fsMetric (ι k)).ρ (blk k z))) hΦ x x' y hy
  · intro x j v hv w hw
    have hysrc : (R.A.chart j).symm v ∈ (R.A.chart j).source := (R.A.chart j).map_target hv.1
    have hyv : (R.A.chart j) ((R.A.chart j).symm v) = v := (R.A.chart j).right_inv hv.1
    obtain ⟨W, hWo, hyW, G, hG, hdiff⟩ := exists_holo_re_eq_sub_of_log_scaling emb
      (fun z => Real.log (∏ k, (fsMetric (ι k)).ρ (blk k z))) hΦ
      x ((R.A.chart j).symm v) ((R.A.chart j).symm v) ⟨hv.2, emb.mem_U _⟩
    have hτ : AnalyticAt ℂ (fun u => R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u)) v :=
      AnalyticAt.pi (fun p => emb.holo ((R.A.chart j).symm v) p j v ⟨hv.1, emb.mem_U _⟩)
    have hmy := emb.mem ((R.A.chart j).symm v) ((R.A.chart j).symm v) (emb.mem_U _)
    have hblk : ∀ k, blk k (R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm v)) ≠ 0 :=
      fun k => blk_ne hmy.1 k
    have hΦy : ContDiffAt ℝ 2 ((fun z : (k : K) × ι k → ℂ => Real.log (∏ k, (fsMetric (ι k)).ρ (blk k z))) ∘
        fun u => R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u)) v :=
      ((contDiffAt_log_prod_fsMetric_rho_blk hblk).comp v (hτ.contDiffAt.restrict_scalars ℝ)).of_le h2
    have hGa : AnalyticAt ℂ (G ∘ (R.A.chart j).symm) v := by
      have := HolomorphicMinorCharts.holo_analyticAt hG j hysrc hyW
      rwa [hyv] at this
    have hRe : ContDiffAt ℝ 2 (fun u => (G ((R.A.chart j).symm u)).re) v :=
      (Complex.reCLM.contDiff.contDiffAt).comp v (hGa.contDiffAt.restrict_scalars ℝ)
    have ht : Filter.Tendsto (R.A.chart j).symm (𝓝 v) (𝓝 ((R.A.chart j).symm v)) := by
      have := HolomorphicMinorCharts.tendsto_symm (R.A.chart j) hysrc
      rwa [hyv] at this
    have hev : ((potOf R Amp).φ x ∘ (R.A.chart j).symm) =ᶠ[𝓝 v]
        fun u => ((fun z : (k : K) × ι k → ℂ => Real.log (∏ k, (fsMetric (ι k)).ρ (blk k z))) ∘
          fun u => R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u)) u +
            1 * (G ((R.A.chart j).symm u)).re := by
      have hW' : ∀ᶠ u in 𝓝 v, (R.A.chart j).symm u ∈ W ∩ R.U x ∩ R.U ((R.A.chart j).symm v) :=
        ht.eventually (((hWo.inter (emb.isOpen x)).inter (emb.isOpen _)).mem_nhds
          ⟨⟨hyW, hv.2⟩, emb.mem_U _⟩)
      filter_upwards [hW'] with u hu
      have := hdiff _ hu
      simp only [Function.comp, one_mul]
      show Real.log (∏ k, (fsMetric (ι k)).ρ (blk k (R.lift x ((R.A.chart j).symm u)))) = _
      linarith
    rw [levi_congr hev, levi_add_smul 1 hΦy hRe]
    have h0 : levi (fun u => (G ((R.A.chart j).symm u)).re) v w = 0 := levi_re_analytic hGa w
    rw [h0, mul_zero, add_zero, levi_comp w hτ ((contDiffAt_log_prod_fsMetric_rho_blk hblk).of_le h2)]
    beta_reduce
    rw [levi_log_prod_fsMetric_eq_sum hblk]
    have hnn : ∀ k, 0 ≤ levi (fun z : ι k → ℂ => Real.log ((fsMetric (ι k)).ρ z))
        (blk k (R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm v)))
        (blk k (fderiv ℂ (fun u => R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u)) v w)) :=
      fun k => GP.levi_fs_nonneg (hblk k) _
    by_contra hle
    push_neg at hle
    have hz0 : ∀ k, levi (fun z : ι k → ℂ => Real.log ((fsMetric (ι k)).ρ z))
        (blk k (R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm v)))
        (blk k (fderiv ℂ (fun u => R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u)) v w)) = 0 :=
      fun k => le_antisymm ((Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ k)).trans hle) (hnn k)
    choose c hc using fun k => GP.levi_fs_zero (hblk k) _ (hz0 k)
    have hdq : ∀ q, fderiv ℂ (fun u => R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u)) v w q =
        c q.1 * R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm v) q := by
      intro q
      have := congrFun (hc q.1) q.2
      simpa [blk] using this
    choose p hp using hmy.1
    have h0' := GP.fderiv_affCoord_zero p hp c hdq
    have himm := emb.immersion _ p hp j hysrc
    rw [hyv] at himm
    have hA := HolomorphicMinorCharts.analyticAt_affCoord p hp
    have hcomp := (hA.differentiableAt.hasFDerivAt.comp v hτ.differentiableAt.hasFDerivAt).fderiv
    have hchain : fderiv ℂ (fun u => affCoord p (R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u))) v w = 0 := by
      have e1 : (fun u => affCoord p (R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u))) =
          affCoord p ∘ fun u => R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u) := rfl
      rw [e1, hcomp, ContinuousLinearMap.comp_apply]
      exact h0'
    have hk : w ∈ LinearMap.ker
        ((fderiv ℂ (fun u => affCoord p (R.lift ((R.A.chart j).symm v) ((R.A.chart j).symm u))) v :
          (Fin e → ℂ) →ₗ[ℂ] ((k : K) × ι k → ℂ))) := LinearMap.mem_ker.2 hchain
    rw [himm] at hk
    exact hw ((Submodule.mem_bot ℂ).1 hk)

end PositivityTheory.UnitarySelfGeneration
