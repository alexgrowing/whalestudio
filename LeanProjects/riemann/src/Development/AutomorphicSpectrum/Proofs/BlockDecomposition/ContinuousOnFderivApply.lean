import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHoldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodularStatement

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.RCalc.ByParts

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_deriv_eq_zero {Γ V : Type*} [TopologicalSpace Γ] [SecondCountableTopology Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] {μ : Measure Γ} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F F' : ℝ → Γ → V} {K : Set Γ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) (C : ℝ)
    (hc : ∀ t ∈ Metric.ball (0 : ℝ) ε, Continuous (F t)) (hc' : Continuous (F' 0))
    (hd : ∀ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun s => F s y) (F' t y) t)
    (hz : ∀ y, y ∉ K → F 0 y = 0)
    (hz' : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y, y ∉ K → F' t y = 0)
    (hb : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y ∈ K, ‖F' t y‖ ≤ C)
    (hconst : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∫ y, F t y ∂μ = ∫ y, F 0 y ∂μ) :
    ∫ y, F' 0 y ∂μ = 0 := by
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    eventually_of_mem hs fun t ht => (hc t ht).aestronglyMeasurable
  have hint : Integrable (F 0) μ :=
    (hc 0 (Metric.mem_ball_self hε)).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hz)
  have hbi : Integrable (K.indicator fun _ => C) μ :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖F' t y‖ ≤ K.indicator (fun _ => C) y :=
    ae_of_all _ fun y t ht => by
      by_cases hy : y ∈ K
      · simpa [hy] using hb t ht y hy
      · simp [hy, hz' t ht y hy]
  have h1 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hint hc'.aestronglyMeasurable hbound hbi
    (ae_of_all _ hd)).2
  have h2 : HasDerivAt (fun t => ∫ y, F t y ∂μ) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (∫ y, F 0 y ∂μ)).congr_of_eventuallyEq ?_
    exact eventually_of_mem hs hconst
  exact h1.unique h2

theorem continuousOn_fderiv_apply {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace P] {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {S : Set P} {A B : P → E} (hA : ContinuousOn A S) (hB : ContinuousOn B S) (hm : MapsTo A S U) :
    ContinuousOn (fun p => fderiv ℝ f (A p) (B p)) S := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.continuousOn.comp hA hm).clm_apply hB

theorem hasDerivAt_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (g v : E) (t : ℝ) (hf : DifferentiableAt ℝ f (g + t • v)) :
    HasDerivAt (fun s : ℝ => f (g + s • v)) (fderiv ℝ f (g + t • v) v) t := by
  have h2 : HasDerivAt (fun s : ℝ => g + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add g
  exact hf.hasFDerivAt.comp_hasDerivAt t h2

variable {n : ℕ}

def c (X : Mat n) (t : ℝ) : Mat n := 1 + t • X

theorem continuous_c (X : Mat n) : Continuous (c X) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem c_zero (X : Mat n) : c X 0 = 1 := by simp [c]

theorem mul_c (y X : Mat n) (t : ℝ) : y * c X t = y + t • (y * X) := by
  simp [c, mul_add]

theorem exists_eps (X : Mat n) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, c X t ∈ GLs n := by
  have h : IsOpen (c X ⁻¹' GLs n) := isOpen_GLs.preimage (continuous_c X)
  have h0 : (0 : ℝ) ∈ c X ⁻¹' GLs n := by simp [c_zero, GLs]
  obtain ⟨ε, hε, h'⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.mem_nhds h0)
  exact ⟨ε, hε, h'⟩

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem mul_mem_GLs' {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  have h : x.det ≠ 0 := hx
  simp [GLs, Matrix.det_nonsing_inv, h]

def toG {x : Mat n} (hx : x ∈ GLs n) : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx

@[simp] theorem toG_val {x : Mat n} (hx : x ∈ GLs n) : (toG hx).val = x := rfl

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem lg_le_lg_mul (hL : LgFacts) (y : G n) {x : Mat n} (hx : x ∈ GLs n) : lg y.val ≤ lg (y.val * x) + lg x := by
  obtain ⟨hsub, hinv, -⟩ := hL n
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have e : y.val = (y.val * x) * x⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  calc lg y.val = lg ((y.val * x) * x⁻¹) := by rw [← e]
    _ ≤ lg (y.val * x) + lg x⁻¹ := hsub _ (mul_mem_GLs' (val_mem_GLs y) hx) _ (inv_mem_GLs hx)
    _ = lg (y.val * x) + lg x := by rw [hinv x hx]

theorem fderiv_eq_zero_far (hL : LgFacts) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V} {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → f y = 0) {x : Mat n} (hx : x ∈ GLs n) (hlg : R < lg x) : fderiv ℝ f x = 0 := by
  obtain ⟨-, -, -, hsm, -⟩ := hL n
  have ho : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := hsm.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have he : f =ᶠ[𝓝 x] fun _ => (0 : V) :=
    eventually_of_mem (ho.mem_nhds ⟨hx, hlg⟩) fun y hy => hR y hy.1 hy.2
  rw [he.fderiv_eq]
  simp

theorem ibp_of (hL : LgFacts) (hU : Unimod) : IBP := by
  intro n _ _ μ _ V _ _ _ f hf hC X
  obtain ⟨R, hR⟩ := hC
  obtain ⟨-, -, -, hsm, hcpt, -⟩ := hL n
  haveI := (hU n μ).1
  haveI : SecondCountableTopology (G n) := secondCountable_G
  obtain ⟨ε, hε, hcε⟩ := exists_eps X
  have hball : ∀ t ∈ Metric.ball (0 : ℝ) ε, c X t ∈ GLs n := fun t ht => hcε t (Metric.ball_subset_closedBall ht)
  have hmem : ∀ (y : G n), ∀ t ∈ Metric.closedBall (0 : ℝ) ε, y.val * c X t ∈ GLs n :=
    fun y t ht => mul_mem_GLs' (val_mem_GLs y) (hcε t ht)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, lg (c X t) ≤ C₀ := by
    have hcont : ContinuousOn (fun t => lg (c X t)) (Metric.closedBall (0 : ℝ) ε) :=
      hsm.continuousOn.comp (continuous_c X).continuousOn hcε
    obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℝ) ε).bddAbove_image hcont
    exact ⟨C₀, fun t ht => hC₀ (mem_image_of_mem _ ht)⟩
  set K : Set (G n) := {y : G n | lg y.val ≤ R + C₀} with hKdef
  have hK : IsCompact K := hcpt (R + C₀)
  have hfar : ∀ (y : G n), y ∉ K → ∀ t ∈ Metric.closedBall (0 : ℝ) ε, R < lg (y.val * c X t) := by
    intro y hy t ht
    have h1 : R + C₀ < lg y.val := not_le.1 hy
    have h2 := lg_le_lg_mul hL y (hcε t ht)
    have h3 := hC₀ t ht
    linarith
  have hvalc : Continuous fun y : G n => y.val := Units.continuous_val
  obtain ⟨C, hCb⟩ : ∃ C, ∀ p ∈ K ×ˢ Metric.closedBall (0 : ℝ) ε,
      ‖fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X)‖ ≤ C := by
    have hcont : ContinuousOn (fun p : G n × ℝ => fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X))
        (K ×ˢ Metric.closedBall (0 : ℝ) ε) := by
      refine continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_
      · exact ((hvalc.comp continuous_fst).mul ((continuous_c X).comp continuous_snd)).continuousOn
      · exact ((hvalc.comp continuous_fst).mul continuous_const).continuousOn
      · exact fun p hp => hmem p.1 p.2 hp.2
    exact (hK.prod (isCompact_closedBall (0 : ℝ) ε)).exists_bound_of_continuousOn hcont
  have key := integral_deriv_eq_zero (μ := μ) (F := fun t (y : G n) => f (y.val * c X t))
    (F' := fun t (y : G n) => fderiv ℝ f (y.val * c X t) (y.val * X)) hK hε C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [c_zero, Rd] using key
  · intro t ht
    exact hf.continuousOn.comp_continuous (hvalc.mul continuous_const)
      fun y => hmem y t (Metric.ball_subset_closedBall ht)
  · refine continuousOn_univ.1 (continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_)
    · exact (hvalc.mul continuous_const).continuousOn
    · exact (hvalc.mul continuous_const).continuousOn
    · exact fun y _ => hmem y 0 (Metric.mem_closedBall_self hε.le)
  · intro y t ht
    have hd : DifferentiableAt ℝ f (y.val + t • (y.val * X)) := by
      rw [← mul_c]
      exact differentiableAt_of_smooth hf (hmem y t (Metric.ball_subset_closedBall ht))
    have := hasDerivAt_line (y.val) (y.val * X) t hd
    have e1 : (fun s : ℝ => f (y.val * c X s)) = fun s : ℝ => f (y.val + s • (y.val * X)) := by
      funext s; rw [mul_c]
    show HasDerivAt (fun s : ℝ => f (y.val * c X s)) (fderiv ℝ f (y.val * c X t) (y.val * X)) t
    rw [e1, mul_c]
    exact this
  · intro y hy
    exact hR _ (hmem y 0 (Metric.mem_closedBall_self hε.le)) (hfar y hy 0 (Metric.mem_closedBall_self hε.le))
  · intro t ht y hy
    have ht' := Metric.ball_subset_closedBall ht
    simp only [fderiv_eq_zero_far hL hR (hmem y t ht') (hfar y hy t ht'), ContinuousLinearMap.zero_apply]
  · intro t ht y hy
    exact hCb (y, t) ⟨hy, Metric.ball_subset_closedBall ht⟩
  · intro t ht
    have h0 := integral_mul_right_eq_self (μ := μ) (fun y : G n => f y.val) (toG (hball t ht))
    simpa [c_zero] using h0

end GlobalTheory.CompanionTheory.RCalc.ByParts

theorem GlobalTheory.CompanionTheory.RCalc.ibp : GlobalTheory.CompanionTheory.RCalc.IBP :=
  GlobalTheory.CompanionTheory.RCalc.ByParts.ibp_of GlobalTheory.T.length_function_facts_hold GlobalTheory.T.general_linear_group_unimodular
