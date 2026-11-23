import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAddFirst
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LogRegLineTensor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LelongChartLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegral
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSection
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongPolyLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre mcPts
  isOpen_blockNonzero)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartComponents mem_segreChartComponents chartLift
  contDiff_chartLift chartLift_blockNonzero segre_chartLift chart_coord_eq_one)

theorem LelongChartLimit.proof (hInt : SegreChartIntegral.Statement) (hDim : SegreChartDim.Statement)
    (hNot : ChartSectionNotMem.Statement) (hLel : LelongPolyLimit.Statement)
    (hDiv : ChartDivisorCompare.Statement) : LelongChartLimit.Statement := by
  classical
  intro K _ _ ι _ P n L A s g i δ hP hL hA hs hg hδ hsupp
  obtain ⟨a, ha, hsa, -⟩ := id hs
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let G := fun x => χ x * g (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  let kk := fun x => A.h (lam x)
  let F := fun (ε : ℝ) x => Real.log (‖eval x (chartSection σ i s)‖ ^ 2 + ε * kk x ^ 2) / 2
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i
  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'
  have hxΩ : ∀ x ∈ segreChartSet P σ i, x ∈ Ω := by
    rintro _ ⟨z, -, hzi, rfl⟩
    exact chartLift_blockNonzero σ i (by simp [σ, hzi])

  have key : ∀ x ∈ segreChartSet P σ i, G =ᶠ[𝓝 x] g ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [G, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    · have hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)
      have hcont : Continuous fun y => segre (lam y) :=
        continuous_pi fun i' => continuous_finsetProd _ fun k _ =>
          (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous
      have hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖} :=
        isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)
      have hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖ := by
        rw [segre_chartLift σ i z hzi, hzi, norm_one]
        have h1 : 1 / δ < ‖segre z‖ := by linarith
        calc (1 : ℝ) = δ * (1 / δ) := by field_simp
          _ < δ * ‖segre z‖ := mul_lt_mul_of_pos_left h1 hδ
      filter_upwards [hO.mem_nhds hx] with y hy
      simp [G, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)

  have hlim := tendsto_finsetSum (segreChartComponents P σ i) fun J hJs =>
    hLel _ n J (chartSection σ i s) G kk Φ (mem_segreChartComponents.1 hJs).1.1
      (hDim K ι P (n + 1) _ σ i hP J hJs) (hNot K ι P (n + 1) _ σ i A s hP hs J hJs)
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm g hg.1)⟩ χ.hasCompactSupport.mul_right
      (fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩) ⟨Ω, hΩ, hJ J hJs, hsm _ hA⟩
      fun x hx => A.pos _ (hJ J hJs hx)
  rw [hDiv K ι P n _ σ i L A s g δ G Φ hP hL hs hg hδ hsupp
    fun x hx => ⟨key x hx, fun j => EventuallyEq.rfl⟩] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)

  set M := (regLine A s ε ha hsa).tensor A
  have hML : ∀ j, IsSmoothHerm ((Fin.cons M L : Fin (n + 1) → HermLine ι) j) :=
    fun j => Fin.cases ((isSmoothHerm_regLine hA hε ha hsa).mul hA) (fun i => hL i) j
  have hcongr : ptsIntegral P
      (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
        (pot L)) g = ptsIntegral P (pot (Fin.cons M L)) g := by
    rw [Inter.PtsAddFirst.pot_cons]
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
    refine Fin.cases ?_ (fun i => ?_) j
    · intro z hz
      simp only [Fin.cons_zero]
      exact (log_regLine_tensor A s hε ha hsa z hz.1).symm
    · intro z _
      simp only [Fin.cons_succ]
  beta_reduce
  rw [hcongr]
  refine (hInt K ι P n _ σ i (Fin.cons M L) g δ G (Matrix.vecCons (F ε) Φ) hP hML hg hδ (Or.inl hsupp)
    fun x hx => ⟨key x hx, fun j => ?_⟩).symm
  refine Fin.cases ?_ (fun j => EventuallyEq.rfl) j
  filter_upwards [hΩ.mem_nhds (hxΩ x hx)] with y hy
  simp only [Matrix.cons_val_zero, Function.comp_apply, Inter.PtsAddFirst.pot_cons, Fin.cons_zero, F, kk,
    eval_chartSection]
  exact (log_regLine_tensor A s hε ha hsa (lam y) hy).symm

end GroundTheory.Heights₂.Heights.Targets
