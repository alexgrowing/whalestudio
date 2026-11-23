import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HermFrame

theorem holo_contDiffOn {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) {m : WithTop ℕ∞} :
    ContDiffOn ℂ m g U := by
  have ha : AnalyticOnNhd ℂ g U := fun z hz =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hU hg hz
  exact ha.contDiffOn hU.uniqueDiffOn

theorem holo_fderiv_apply_on {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    DifferentiableOn ℂ (fun u => fderiv ℂ g u w) U := by
  have h2 : ContDiffOn ℂ 2 g U := holo_contDiffOn hU hg
  have h1 : ContDiffOn ℂ 1 (fun u => fderiv ℂ g u) U := h2.fderiv_of_isOpen hU (by norm_num)
  exact (h1.clm_apply contDiffOn_const).differentiableOn (by norm_num)

theorem holo_del_eq_on {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) {u : ReciprocityTheory.L2DbarEstimates.V n}
    (hu : u ∈ U) (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.del g u w = fderiv ℂ g u w := by
  rw [GlobalTheory.del_eq_fderiv (hg.differentiableAt (hU.mem_nhds hu))]

end GlobalTheory.HermFrame

namespace GlobalTheory.HermFrame

theorem holo_mdel_entry {n : ℕ} {K : Type} {P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ}
    {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) U)
    {u : ReciprocityTheory.L2DbarEstimates.V n} (hu : u ∈ U) (w : ReciprocityTheory.L2DbarEstimates.V n) (i k : K) :
    mdel P u w i k = fderiv ℂ (fun x => P x i k) u w :=
  holo_del_eq_on hU (hP i k) hu w

theorem holo_mdel_mdel_entry {n : ℕ} {K : Type} {P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ}
    {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) U)
    {u : ReciprocityTheory.L2DbarEstimates.V n} (hu : u ∈ U) (w w' : ReciprocityTheory.L2DbarEstimates.V n) (i k : K) :
    mdel (fun x => mdel P x w') u w i k =
      fderiv ℂ (fun x => fderiv ℂ (fun y => P y i k) x w') u w := by
  change GlobalTheory.del (fun x => GlobalTheory.del (fun y => P y i k) x w') u w = _
  have hev : (fun x => GlobalTheory.del (fun y => P y i k) x w') =ᶠ[𝓝 u]
      (fun x => fderiv ℂ (fun y => P y i k) x w') := by
    filter_upwards [hU.mem_nhds hu] with x hx
    exact holo_del_eq_on hU (hP i k) hx w'
  rw [GlobalTheory.del_congr hev]
  exact holo_del_eq_on hU (holo_fderiv_apply_on hU (hP i k) w') hu w

theorem holoFrame_local_bounds : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (r : ℝ), 0 < r → (∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r)) → IsUnit (P 0).det → ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ B : ℝ, ∀ v : ReciprocityTheory.L2DbarEstimates.V n, ‖v‖ < r' → IsUnit (P v).det ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) ∧ (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) ∧ (∀ i k, ‖P v i k‖ ≤ B) ∧ (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) ∧ (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) ∧ (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) := by
  intro n K _ _ P r hr hP h0
  set U : Set (ReciprocityTheory.L2DbarEstimates.V n) := Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hPc : ContinuousOn P U :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => (hP i k).continuousOn
  have hdetc : ContinuousOn (fun u => (P u).det) U :=
    (continuous_id.matrix_det).comp_continuousOn hPc
  have hadjc : ∀ i k, ContinuousOn (fun u => (P u).adjugate i k) U := fun i k =>
    ((continuous_id.matrix_adjugate).matrix_elem i k).comp_continuousOn hPc
  have h0U : (0 : ReciprocityTheory.L2DbarEstimates.V n) ∈ U := Metric.mem_ball_self hr
  have hev : ∀ᶠ u in 𝓝 (0 : ReciprocityTheory.L2DbarEstimates.V n), (P u).det ≠ 0 :=
    (hdetc.continuousAt (hU.mem_nhds h0U)).eventually_ne h0.ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hm : 0 < min ε r := lt_min hε hr
  set ρ := min ε r / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hρε : ρ < ε := by have := min_le_left ε r; rw [hρ]; linarith
  have hρr : ρ < r := by have := min_le_right ε r; rw [hρ]; linarith
  set S := Metric.closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) ρ with hSdef
  have hSU : S ⊆ U := Metric.closedBall_subset_ball hρr
  have hSdet : ∀ u ∈ S, (P u).det ≠ 0 := fun u hu =>
    hball u (Metric.closedBall_subset_ball hρε hu)
  have hSc : IsCompact S := isCompact_closedBall 0 ρ

  let G1 : ReciprocityTheory.L2DbarEstimates.V n → (K → K → ℂ) := fun u i k => P u i k
  let G2 : ReciprocityTheory.L2DbarEstimates.V n → (K → K → ℂ) := fun u i k => (P u)⁻¹ i k
  let G3 : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → K → K → ℂ) := fun u a i k =>
    mdel P u (GlobalTheory.GoodMetric.coordVec a) i k
  let G4 : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → Fin n → K → K → ℂ) := fun u a b i k =>
    mdel (fun u => mdel P u (GlobalTheory.GoodMetric.coordVec b)) u (GlobalTheory.GoodMetric.coordVec a) i k
  have hG1 : ContinuousOn G1 S :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ((hP i k).continuousOn).mono hSU
  have hG2 : ContinuousOn G2 S := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    refine (((hdetc.mono hSU).inv₀ hSdet).mul ((hadjc i k).mono hSU)).congr fun u _ => ?_
    simp [G2, Matrix.inv_def, Ring.inverse_eq_inv']
  have hG3 : ContinuousOn G3 S := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    refine ((holo_fderiv_apply_on hU (hP i k) (GlobalTheory.GoodMetric.coordVec a)).continuousOn.mono
      hSU).congr fun u hu => ?_
    exact holo_mdel_entry hU hP (hSU hu) _ i k
  have hG4 : ContinuousOn G4 S := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => continuousOn_pi.2 fun i =>
      continuousOn_pi.2 fun k => ?_
    refine ((holo_fderiv_apply_on hU (holo_fderiv_apply_on hU (hP i k)
      (GlobalTheory.GoodMetric.coordVec b)) (GlobalTheory.GoodMetric.coordVec a)).continuousOn.mono hSU).congr
      fun u hu => ?_
    exact holo_mdel_mdel_entry hU hP (hSU hu) _ _ i k
  obtain ⟨C1, hC1⟩ := hSc.exists_bound_of_continuousOn hG1
  obtain ⟨C2, hC2⟩ := hSc.exists_bound_of_continuousOn hG2
  obtain ⟨C3, hC3⟩ := hSc.exists_bound_of_continuousOn hG3
  obtain ⟨C4, hC4⟩ := hSc.exists_bound_of_continuousOn hG4
  refine ⟨ρ, hρpos, hρr.le, max (max C1 C2) (max C3 C4), fun v hv => ?_⟩
  have hvS : v ∈ S := by
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hvU : v ∈ U := hSU hvS
  refine ⟨isUnit_iff_ne_zero.2 (hSdet v hvS), fun i k => ?_, ?_, fun i k => ?_, fun i k => ?_,
    fun a i k => ?_, fun a b i k => ?_⟩
  · exact ((holo_contDiffOn hU (hP i k)).contDiffAt (hU.mem_nhds hvU)).restrict_scalars ℝ
  · filter_upwards [hU.mem_nhds hvU] with u hu η
    ext i k
    simp [GlobalTheory.dbar_eq_zero ((hP i k).differentiableAt (hU.mem_nhds hu))]
  · have h := (norm_le_pi_norm (G1 v i) k).trans ((norm_le_pi_norm (G1 v) i).trans (hC1 v hvS))
    exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h := (norm_le_pi_norm (G2 v i) k).trans ((norm_le_pi_norm (G2 v) i).trans (hC2 v hvS))
    exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
  · have h := (norm_le_pi_norm (G3 v a i) k).trans ((norm_le_pi_norm (G3 v a) i).trans
      ((norm_le_pi_norm (G3 v) a).trans (hC3 v hvS)))
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h := (norm_le_pi_norm (G4 v a b i) k).trans ((norm_le_pi_norm (G4 v a b) i).trans
      ((norm_le_pi_norm (G4 v a) b).trans ((norm_le_pi_norm (G4 v) a).trans (hC4 v hvS))))
    exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

end GlobalTheory.HermFrame
