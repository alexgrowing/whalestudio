import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IntegrableAbsThetaToReal

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ} {V : HSp D}

structure Fam (V : HSp D) (ν : Measure (GA D V)) (U : Set ℂ) (f : ℂ → Mx D V.rank n → ℂ) : Prop where
  diff : ∀ x, DifferentiableOn ℂ (fun z => f z x) U
  maj : ∀ z₀ ∈ U, ∃ ε > 0, Metric.ball z₀ ε ⊆ U ∧ ∃ M : Mx D V.rank n → ℂ, Continuous M ∧ absThetaInt V ν M < ⊤ ∧
    ∀ z ∈ Metric.ball z₀ ε, ∀ x, ‖f z x‖ ≤ ‖M x‖
  meas : ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (f z))) (autMeasure V ν)

def dF (f : ℂ → Mx D V.rank n → ℂ) : ℂ → Mx D V.rank n → ℂ := fun z x => deriv (fun w => f w x) z

def iF (f : ℂ → Mx D V.rank n → ℂ) (r : ℕ) : ℂ → Mx D V.rank n → ℂ := fun z x => iteratedDeriv r (fun w => f w x) z

theorem iF_zero (f : ℂ → Mx D V.rank n → ℂ) : iF f 0 = f := by
  funext z x; simp [iF]

theorem iF_succ (f : ℂ → Mx D V.rank n → ℂ) (r : ℕ) : iF f (r + 1) = dF (iF f r) := by
  funext z x; simp only [iF, dF, iteratedDeriv_succ]

theorem cauchy_le {g : ℂ → ℂ} {U : Set ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} {r C : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall z r ⊆ U) (hC : ∀ w ∈ Metric.sphere z r, ‖g w‖ ≤ C) : ‖deriv g z‖ ≤ C / r := by
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ hC
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball z hr.ne']
  exact hg.mono hsub

theorem fam_hasDeriv (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    AEStronglyMeasurable (descend (GQ V) (thS V (dF f z₀))) (autMeasure V ν) ∧
    HasDerivAt (fun z => ∫ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν)
      (∫ q, descend (GQ V) (thS V (dF f z₀)) q ∂autMeasure V ν) z₀ := by
  obtain ⟨ε, hε, hball, M, hMc, hMfin, hMb⟩ := hf.maj z₀ hz₀
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsubU : ∀ z ∈ Metric.ball z₀ r, Metric.closedBall z r ⊆ U := by
    intro z hz w hw
    apply hball
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_closedBall] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r + r := by linarith
      _ ≤ ε := by rw [hr]; linarith
  have hmemM : ∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.sphere z r, w ∈ Metric.ball z₀ ε := by
    intro z hz w hw
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_sphere] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r + r := by linarith
      _ ≤ ε := by rw [hr]; linarith
  have hcb : ∀ z ∈ Metric.ball z₀ r, ∀ x, ‖dF f z x‖ ≤ ‖M x‖ / r := fun z hz x =>
    cauchy_le (hf.diff x) hr0 (hsubU z hz) fun w hw => hMb w (hmemM z hz w hw) x
  have hballU : Metric.ball z₀ r ⊆ U := fun z hz => hsubU z hz (Metric.mem_closedBall_self hr0.le)
  have hz₀r : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr0
  have hz₀ε : z₀ ∈ Metric.ball z₀ ε := Metric.mem_ball_self hε

  have hfinq := ae_absTheta_lt V ν hMc hMfin
  have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
      Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
    intro q hq
    refine Summable.of_enorm ?_
    simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
  have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ = (descend (GQ V) (absTheta V M) q).toReal := by
    intro q hq
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
    rw [ENNReal.tsum_toReal_eq fun ξ => enorm_ne_top]
    simp

  have hdiff : ∀ᵐ q ∂autMeasure V ν, ∀ z ∈ Metric.ball z₀ r,
      HasDerivAt (fun z => descend (GQ V) (thS V (f z)) q) (descend (GQ V) (thS V (dF f z)) q) z := by
    filter_upwards [hfinq] with q hq z hz
    have hs := hsumM q hq
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
    refine hasDerivAt_tsum_of_isPreconnected (u := fun ξ => ‖M (invPt V q.out ξ)‖ / r) (hs.div_const r)
      Metric.isOpen_ball (convex_ball z₀ r).isPreconnected (fun ξ y hy => ?_) (fun ξ y hy => hcb y hy _) hz₀r ?_ hz
    · exact ((hf.diff _).differentiableAt (hU.mem_nhds (hballU hy))).hasDerivAt
    · exact Summable.of_norm_bounded hs fun ξ => hMb z₀ hz₀ε _

  have hmeas' : AEStronglyMeasurable (descend (GQ V) (thS V (dF f z₀))) (autMeasure V ν) := by
    let s : ℕ → ℂ := fun k => z₀ + ((r / 2 / ((k : ℝ) + 1) : ℝ) : ℂ)
    have hs_ne : ∀ k, s k ≠ z₀ := by
      intro k h
      have : ((r / 2 / ((k : ℝ) + 1) : ℝ) : ℂ) = 0 := by simpa [s] using h
      have h2 : r / 2 / ((k : ℝ) + 1) ≠ 0 := by positivity
      exact h2 (by exact_mod_cast this)
    have hs_mem : ∀ k, s k ∈ Metric.ball z₀ r := by
      intro k
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [s, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      calc r / 2 / ((k : ℝ) + 1) ≤ r / 2 := div_le_self (by positivity) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        _ < r := by linarith
    have hs_lim : Tendsto s atTop (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hs_ne⟩
      have : Tendsto (fun k : ℕ => r / 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (r / 2)
        rw [mul_zero] at h0
        refine h0.congr fun k => ?_
        ring
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
      simpa [s] using (tendsto_const_nhds (x := z₀)).add h2
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun k q => (s k - z₀)⁻¹ • (descend (GQ V) (thS V (f (s k))) q - descend (GQ V) (thS V (f z₀)) q))
      (fun k => ((hf.meas _ (hballU (hs_mem k))).sub (hf.meas _ hz₀)).const_smul (s k - z₀)⁻¹) ?_
    filter_upwards [hdiff] with q hq
    have hd := hq z₀ hz₀r
    exact (hasDerivAt_iff_tendsto_slope.1 hd).comp hs_lim
  refine ⟨hmeas', ?_⟩
  have hint0 : Integrable (descend (GQ V) (thS V (f z₀))) (autMeasure V ν) := by
    refine ⟨hf.meas _ hz₀, lt_of_le_of_lt (lintegral_mono fun q => ?_) (lt_of_le_of_lt (le_refl _) hMfin)⟩
    exact (enorm_thS_le V _ q.out).trans (absTheta_mono V (hMb z₀ hz₀ε) q.out)
  have hbound : ∀ᵐ q ∂autMeasure V ν, ∀ z ∈ Metric.ball z₀ r,
      ‖descend (GQ V) (thS V (dF f z)) q‖ ≤ (descend (GQ V) (absTheta V M) q).toReal / r := by
    filter_upwards [hfinq] with q hq z hz
    have hs := hsumM q hq
    have hs' : Summable fun ξ => ‖dF f z (invPt V q.out ξ)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb z hz _) (hs.div_const r)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS] at *
    calc ‖∑' ξ, dF f z (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖dF f z (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
      _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ / r := hs'.tsum_le_tsum (fun ξ => hcb z hz _) (hs.div_const r)
      _ = (∑' ξ, ‖M (invPt V q.out ξ)‖) / r := tsum_div_const
      _ = _ := by rw [htsM q hq]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ hr0) (Eventually.mono (hU.mem_nhds hz₀) fun z hz => hf.meas z hz)
    hint0 hmeas' hbound ((integrable_absTheta_toReal V ν hMc hMfin).div_const r) hdiff).2

theorem fam_dF (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) : Fam V ν U (dF f) where
  diff x := (hf.diff x).deriv hU
  maj z₀ hz₀ := by
    obtain ⟨ε, hε, hball, M, hMc, hMfin, hMb⟩ := hf.maj z₀ hz₀
    refine ⟨ε / 2, by positivity, (Metric.ball_subset_ball (by linarith)).trans hball, ((2 / ε : ℝ) : ℂ) • M,
      hMc.const_smul _, absThetaInt_smul_lt V ν _ hMfin, ?_⟩
    intro z hz x
    have hsub : Metric.closedBall z (ε / 2) ⊆ U := by
      intro w hw
      apply hball
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_closedBall] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have hmem : ∀ w ∈ Metric.sphere z (ε / 2), w ∈ Metric.ball z₀ ε := by
      intro w hw
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_sphere] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have h := cauchy_le (hf.diff x) (by positivity : (0 : ℝ) < ε / 2) hsub fun w hw => hMb w (hmem w hw) x
    calc ‖dF f z x‖ ≤ ‖M x‖ / (ε / 2) := h
      _ = ‖(((2 / ε : ℝ) : ℂ) • M) x‖ := by
        rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
  meas z hz := (fam_hasDeriv V ν hU hf hz).1

theorem fam_iF (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) (r : ℕ) : Fam V ν U (iF f r) := by
  induction r with
  | zero => rwa [iF_zero]
  | succ r ih => rw [iF_succ]; exact fam_dF V ν hU ih

theorem iteratedDeriv_avg (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) (r : ℕ) :
    ∀ z ∈ U, iteratedDeriv r (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) z =
      ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν := by
  have hder : ∀ r, ∀ z ∈ U, HasDerivAt (fun z => ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν)
      (⨍ q, descend (GQ V) (thS V (iF f (r + 1) z)) q ∂autMeasure V ν) z := by
    intro r z hz
    simp only [average_eq]
    rw [iF_succ]
    exact (fam_hasDeriv V ν hU (fam_iF V ν hU hf r) hz).2.const_smul _
  induction r with
  | zero => intro z _; simp [iF_zero]
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv r (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) =ᶠ[𝓝 z]
        fun z => ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν :=
      Eventually.mono (hU.mem_nhds hz) fun w hw => ih w hw
    rw [heq.deriv_eq]
    exact (hder r z hz).deriv

theorem differentiableOn_avg (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) :
    DifferentiableOn ℂ (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) U := by
  intro z hz
  simp only [average_eq]
  exact ((fam_hasDeriv V ν hU hf hz).2.const_smul _).differentiableAt.differentiableWithinAt

end PositivityTheory.Rg.Sw.Glob.DHolH
