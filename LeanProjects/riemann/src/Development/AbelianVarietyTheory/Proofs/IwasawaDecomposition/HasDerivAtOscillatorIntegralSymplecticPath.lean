import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtLineDH
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivEqQuadComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedVacuumDeriv

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.OscDeriv

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}

set_option linter.unusedSectionVars false

noncomputable def omL (J : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).bilinearComp (ContinuousLinearMap.id ℝ V)
    (J.toContinuousLinearEquiv : V →L[ℝ] V)

theorem hasDerivAt_heis (h : IsHeis (omJ J) ρ) {b : ℝ → V} {Y : ℝ → B} {b' : V} {Y' : B} (hb : HasDerivAt b b' 0)
    (hY : HasDerivAt Y Y' 0) (hs : Sm ρ (Y 0)) :
    HasDerivAt (fun t => ρ (b t) (Y t)) (ρ (b 0) Y' + fderiv ℝ (fun u => ρ u (Y 0)) (b 0) b') 0 := by
  have h1 : HasDerivAt (fun t => ρ (b t) (Y 0)) (fderiv ℝ (fun u => ρ u (Y 0)) (b 0) b') 0 :=
    (ContDiff.differentiable hs (by simp) (b 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hb
  have h2 : HasDerivAt (fun t => ρ (b t) (Y t - Y 0)) (ρ (b 0) Y') 0 := by
    rw [hasDerivAt_iff_tendsto_slope] at hY ⊢
    have hc : Continuous fun p : V × B => ρ p.1 p.2 := h.continuous continuous_fst continuous_snd
    have := (hc.tendsto (b 0, Y')).comp ((hb.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).prodMk_nhds hY)
    refine this.congr fun t => ?_
    simp [slope]
  simpa using h2.fun_add h1

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma omL_apply_eq_omJ (x y : V) :
    _root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x y = _root_.GlobalTheory.RealWeil.omJ J x y := by
  simp [_root_.GlobalTheory.Mem.Lift.OscDeriv.omL, _root_.GlobalTheory.RealWeil.omJ]

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma omL_eq_omJ :
    (fun x y => _root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x y) = _root_.GlobalTheory.RealWeil.omJ J := by
  funext x y; exact omL_apply_eq_omJ x y

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma omL_self_eq_zero (hJ : ∀ x, J (J x) = -x) (x : V) :
    _root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x x = 0 := by
  rw [omL_apply_eq_omJ]
  unfold _root_.GlobalTheory.RealWeil.omJ
  have h1 := J.inner_map_map x (J x)
  rw [hJ, inner_neg_right, real_inner_comm] at h1
  linarith

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma integrable_of_quadratic_weight {μ : Measure V} {g : V → ℝ}
    (hg : ∀ n : ℕ, Integrable (fun w => ‖w‖ ^ n * g w) μ) {G : V → B}
    (hGm : AEStronglyMeasurable G μ) (a b c : ℝ)
    (hb : ∀ w, ‖G w‖ ≤ (a + b * ‖w‖ + c * ‖w‖ ^ 2) * g w) : Integrable G μ := by
  have hi := ((hg 0).const_mul a).add (((hg 1).const_mul b).add ((hg 2).const_mul c))
  refine Integrable.mono' (hi.congr (ae_of_all _ fun w => ?_)) hGm (ae_of_all _ hb)
  simp only [pow_zero, pow_one, Pi.add_apply]; ring

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma aestronglyMeasurable_dH_comp {μ : Measure V} {G : V → B}
    (hGm : AEStronglyMeasurable G μ) (hG : ∀ w, _root_.GlobalTheory.RealWeil.Sm ρ (G w)) (v : V) :
    AEStronglyMeasurable (fun w => _root_.GlobalTheory.Mem.Lift.dH ρ v (G w)) μ := by
  have hlim : ∀ w, Filter.Tendsto (fun t : ℝ => t⁻¹ • (ρ ((0 + t) • v) (G w) - ρ ((0:ℝ) • v) (G w)))
      (𝓝[≠] 0) (𝓝 (_root_.GlobalTheory.Mem.Lift.dH ρ v (G w))) := fun w =>
    (hasDerivAt_iff_tendsto_slope_zero.1 (_root_.GlobalTheory.Mem.Lift.hasDerivAt_dH v (hG w)))
  exact aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0:ℝ))
    (fun t => (((ρ _).continuous.comp_aestronglyMeasurable hGm).sub
      ((ρ _).continuous.comp_aestronglyMeasurable hGm)).const_smul _) (ae_of_all _ hlim)

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma abs_omL_apply_le (x y : V) :
    |_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x y| ≤ ‖x‖ * ‖y‖ := by
  rw [omL_apply_eq_omJ]
  unfold _root_.GlobalTheory.RealWeil.omJ
  calc |⟪x, J y⟫| ≤ ‖x‖ * ‖J y‖ := abs_real_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [LinearIsometryEquiv.norm_map]

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma norm_dH_action_le (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) {z : B}
    (hz : _root_.GlobalTheory.RealWeil.Sm ρ z) (v w : V) :
    ‖_root_.GlobalTheory.Mem.Lift.dH ρ v (ρ w z)‖ ≤ ‖_root_.GlobalTheory.Mem.Lift.dH ρ v z‖ + 2 * π * (‖v‖ * ‖w‖) * ‖z‖ := by
  have hb : _root_.GlobalTheory.RealWeil.IsHeis (fun x y => _root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x y) ρ := by
    rw [omL_eq_omJ]; exact h
  rw [(_root_.GlobalTheory.Mem.Lift.DCalc.dH_calculus V B _ ρ (omL_self_eq_zero hJ) hb z hz).2.2.2.1 v w]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, h.2.2.1, h.2.2.1]
  have := abs_omL_apply_le (J := J) v w
  have hn : ‖(2 * (π:ℂ) * Complex.I * ((_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J v w : ℝ) : ℂ))‖ = 2 * π * |_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J v w| := by
    simp [abs_of_pos Real.pi_pos]
  rw [hn]; gcongr

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma quad_integral_eq_integral_quad (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ)
    {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) {μ : Measure V} {F : V → B}
    (hF : Integrable F μ) (hFs : ∀ w, _root_.GlobalTheory.RealWeil.Sm ρ (F w))
    (hIs : _root_.GlobalTheory.RealWeil.Sm ρ (∫ w, F w ∂μ))
    (hD1 : ∀ v, Integrable (fun w => _root_.GlobalTheory.Mem.Lift.dH ρ v (F w)) μ)
    (hD2 : ∀ u v, Integrable (fun w => _root_.GlobalTheory.Mem.Lift.dH ρ u (_root_.GlobalTheory.Mem.Lift.dH ρ v (F w))) μ) :
    _root_.GlobalTheory.Mem.Lift.quad ρ c p q (∫ w, F w ∂μ) = ∫ w, _root_.GlobalTheory.Mem.Lift.quad ρ c p q (F w) ∂μ := by
  have hb : _root_.GlobalTheory.RealWeil.IsHeis (fun x y => _root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x y) ρ := by
    rw [omL_eq_omJ]; exact h
  have hself := omL_self_eq_zero (J := J) hJ
  have comm1 : ∀ v, _root_.GlobalTheory.Mem.Lift.dH ρ v (∫ w, F w ∂μ) = ∫ w, _root_.GlobalTheory.Mem.Lift.dH ρ v (F w) ∂μ :=
    fun v => _root_.GlobalTheory.Mem.Lift.dH_integral V B _ ρ hself hb V μ F hFs hF hIs v (hD1 v)
  have comm2 : ∀ u v, _root_.GlobalTheory.Mem.Lift.dH ρ u (∫ w, _root_.GlobalTheory.Mem.Lift.dH ρ v (F w) ∂μ) =
      ∫ w, _root_.GlobalTheory.Mem.Lift.dH ρ u (_root_.GlobalTheory.Mem.Lift.dH ρ v (F w)) ∂μ := by
    intro u v
    refine _root_.GlobalTheory.Mem.Lift.dH_integral V B _ ρ hself hb V μ _
      (fun w => (_root_.GlobalTheory.Mem.Lift.DCalc.dH_calculus V B _ ρ hself hb _ (hFs w)).1 v) (hD1 v) ?_ u (hD2 u v)
    rw [← comm1]
    exact (_root_.GlobalTheory.Mem.Lift.DCalc.dH_calculus V B _ ρ hself hb _ hIs).1 v
  unfold _root_.GlobalTheory.Mem.Lift.quad
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul, comm1, comm2]
  · intro i _
    exact (hD2 _ _).smul (c i)

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma norm_heis_action_sub_le (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) {y : B}
    (hy : _root_.GlobalTheory.RealWeil.Sm ρ y) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : V, ‖_root_.GlobalTheory.Mem.Lift.dH ρ s y‖ ≤ C * ‖s‖ * ‖y‖) {R : ℝ} {w w' : V}
    (hw : ‖w‖ ≤ R) (hw' : ‖w'‖ ≤ R) :
    ‖ρ w' y - ρ w y‖ ≤ (C + π * R) * ‖y‖ * ‖w' - w‖ := by
  have hb : _root_.GlobalTheory.RealWeil.IsHeis (fun x y => _root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x y) ρ := by
    rw [omL_eq_omJ]; exact h
  have hcal := _root_.GlobalTheory.Mem.Lift.DCalc.dH_calculus V B _ ρ (omL_self_eq_zero hJ) hb y hy
  have hcd : ContDiff ℝ ∞ (fun v => ρ v y) := hy
  have hdiff : Differentiable ℝ (fun v => ρ v y) := hcd.differentiable (by simp)
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  refine (convex_closedBall (0:V) R).norm_image_sub_le_of_norm_fderiv_le
    (fun u _ => hdiff u) (fun u hu => ?_) (by simpa using hw) (by simpa using hw')
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun s => ?_
  rw [hcal.2.2.1 u s]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, h.2.2.1, h.2.2.1]
  have h1 := abs_omL_apply_le (J := J) u s
  have hn : ‖((π:ℂ) * Complex.I * ((_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J u s : ℝ) : ℂ))‖ = π * |_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J u s| := by
    simp [abs_of_pos Real.pi_pos]
  rw [hn]
  have h2 : π * |_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J u s| ≤ π * (R * ‖s‖) :=
    mul_le_mul_of_nonneg_left (h1.trans (by gcongr)) Real.pi_pos.le
  calc ‖_root_.GlobalTheory.Mem.Lift.dH ρ s y‖ + π * |_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J u s| * ‖y‖
      ≤ C * ‖s‖ * ‖y‖ + π * (R * ‖s‖) * ‖y‖ := by gcongr; exact hC s
    _ = (C + π * R) * ‖y‖ * ‖s‖ := by ring

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in
private lemma tendsto_heis_action_apply {om : V → V → ℝ} (h : _root_.GlobalTheory.RealWeil.IsHeis om ρ)
    {ι : Type} {l : Filter ι} {u : ι → V} {v : ι → B} {u₀ : V} {v₀ : B}
    (hu : Filter.Tendsto u l (𝓝 u₀)) (hv : Filter.Tendsto v l (𝓝 v₀)) :
    Filter.Tendsto (fun i => ρ (u i) (v i)) l (𝓝 (ρ u₀ v₀)) := by
  have h1 : Filter.Tendsto (fun i => ρ (u i) v₀) l (𝓝 (ρ u₀ v₀)) :=
    ((h.2.2.2 v₀).tendsto u₀).comp hu
  rw [tendsto_iff_norm_sub_tendsto_zero] at hv h1 ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (by simpa using hv.add h1)
  calc ‖ρ (u i) (v i) - ρ u₀ v₀‖ = ‖ρ (u i) (v i - v₀) + (ρ (u i) v₀ - ρ u₀ v₀)‖ := by
        rw [map_sub, sub_add_sub_cancel]
    _ ≤ ‖ρ (u i) (v i - v₀)‖ + ‖ρ (u i) v₀ - ρ u₀ v₀‖ := norm_add_le _ _
    _ = ‖v i - v₀‖ + ‖ρ (u i) v₀ - ρ u₀ v₀‖ := by rw [h.2.2.1]

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B} in
set_option linter.unusedSectionVars false in

theorem _root_.GlobalTheory.Mem.Lift.OscDeriv.hasDerivAt_osc : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ, ∀ (a : ℝ → V →L[ℝ] V) (X : V →L[ℝ] V), a 0 = 1 → HasDerivAt a X 0 → (∀ t x y, _root_.GlobalTheory.RealWeil.omJ J (a t x) (a t y) = _root_.GlobalTheory.RealWeil.omJ J x y) → ∀ (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), _root_.GlobalTheory.Mem.Lift.IsQuadOf (_root_.GlobalTheory.RealWeil.omJ J) X c p q → ∃ lam : ℂ, ∀ f, _root_.GlobalTheory.RealWeil.Sm ρ f → HasDerivAt (fun t : ℝ => ∫ w, ρ (a t w) (∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ (a t u) (_root_.GlobalTheory.RealWeil.proj h (ρ (-w) f)))) (_root_.GlobalTheory.Mem.Lift.quad ρ c p q f + lam • f) 0 := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h a X ha0 hX hsym κ _ c p q hQ
  obtain ⟨⟨C0, hC0⟩, lam, hlam⟩ :=
    _root_.GlobalTheory.Mem.Lift.MovedVac.moved_vacuum_deriv V B J ρ hJ h a X ha0 hX hsym κ c p q hQ
  obtain ⟨⟨C1, hC1⟩, hC2, -⟩ := _root_.GlobalTheory.Mem.Lift.VacBd.vacuum_bound V B J ρ hJ h
  refine ⟨lam, fun f hf => ?_⟩
  have hb : _root_.GlobalTheory.RealWeil.IsHeis (fun x y => _root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x y) ρ := by
    rw [omL_eq_omJ]; exact h
  have hself := omL_self_eq_zero (J := J) hJ
  have hQ' : _root_.GlobalTheory.Mem.Lift.IsQuadOf (fun x y => _root_.GlobalTheory.Mem.Lift.OscDeriv.omL J x y) X c p q := by
    rw [omL_eq_omJ]; exact hQ
  have hPP : ∀ x, _root_.GlobalTheory.RealWeil.proj h (_root_.GlobalTheory.RealWeil.proj h x) = _root_.GlobalTheory.RealWeil.proj h x :=
    _root_.GlobalTheory.RealWeil.Osc.proj_proj hJ h
  have hPs : ∀ x, _root_.GlobalTheory.RealWeil.Sm ρ (_root_.GlobalTheory.RealWeil.proj h x) := fun x =>
    _root_.GlobalTheory.RealWeil.Good.sm hJ (_root_.GlobalTheory.RealWeil.Osc.good_proj hJ h x)
  have hrd : _root_.GlobalTheory.RealWeil.Good h f := _root_.GlobalTheory.RealWeil.Osc.good_of_sm hJ h hf
  have hint : ∀ n : ℕ, Integrable (fun w : V => ‖w‖ ^ n * ‖_root_.GlobalTheory.RealWeil.proj h (ρ (-w) f)‖) := by
    intro n; exact hrd n
  have hres : ∫ w, ρ w (_root_.GlobalTheory.RealWeil.proj h (ρ (-w) f)) = f :=
    _root_.GlobalTheory.RealWeil.Good.inversion hJ hrd
  obtain ⟨y, hy⟩ : ∃ y : V → B, y = fun w => _root_.GlobalTheory.RealWeil.proj h (ρ (-w) f) := ⟨_, rfl⟩
  have hyP : ∀ w, _root_.GlobalTheory.RealWeil.proj h (y w) = y w := fun w => by rw [hy]; exact hPP _
  have hys : ∀ w, _root_.GlobalTheory.RealWeil.Sm ρ (y w) := fun w => by rw [hy]; exact hPs _
  obtain ⟨C1', hC1'0, hC1'⟩ : ∃ C, 0 ≤ C ∧ ∀ w s, ‖_root_.GlobalTheory.Mem.Lift.dH ρ s (y w)‖ ≤ C * ‖s‖ * ‖y w‖ := by
    refine ⟨max C1 0, le_max_right _ _, fun w s => ?_⟩
    have := hC1 s (y w)
    rw [hyP] at this
    exact this.trans (by gcongr; exact le_max_left _ _)
  have hint' : ∀ n : ℕ, Integrable (fun w : V => ‖w‖ ^ n * ‖y w‖) := by rw [hy]; exact hint
  have hres' : ∫ w, ρ w (y w) = f := by rw [hy]; exact hres
  have hFi : Integrable (fun w => ρ w (y w)) := by
    rw [hy]; exact _root_.GlobalTheory.RealWeil.Osc.intw_integrable (T := _root_.GlobalTheory.RealWeil.proj h) h hPP hrd
  have hcal := fun z (hz : _root_.GlobalTheory.RealWeil.Sm ρ z) =>
    _root_.GlobalTheory.Mem.Lift.DCalc.dH_calculus V B _ ρ hself hb z hz
  have hFs : ∀ w, _root_.GlobalTheory.RealWeil.Sm ρ (ρ w (y w)) := fun w => (hcal _ (hys w)).2.1 w
  have hD1 : ∀ v, Integrable (fun w => _root_.GlobalTheory.Mem.Lift.dH ρ v (ρ w (y w))) := by
    intro v
    refine integrable_of_quadratic_weight hint'
      (aestronglyMeasurable_dH_comp hFi.aestronglyMeasurable hFs v) (C1' * ‖v‖) (2 * π * ‖v‖) 0
      (fun w => ?_)
    calc _ ≤ _ := norm_dH_action_le hJ h (hys w) v w
      _ ≤ C1' * ‖v‖ * ‖y w‖ + 2 * π * (‖v‖ * ‖w‖) * ‖y w‖ := by gcongr; exact hC1' w v
      _ = _ := by ring
  have hD2 : ∀ u v, Integrable (fun w => _root_.GlobalTheory.Mem.Lift.dH ρ u (_root_.GlobalTheory.Mem.Lift.dH ρ v (ρ w (y w)))) := by
    intro u v
    obtain ⟨C2, hC2'⟩ := hC2 u v
    refine integrable_of_quadratic_weight hint'
      (aestronglyMeasurable_dH_comp
        (aestronglyMeasurable_dH_comp hFi.aestronglyMeasurable hFs v)
        (fun w => (hcal _ (hFs w)).1 v) u)
      C2 (4 * π * C1' * ‖u‖ * ‖v‖) (4 * π ^ 2 * ‖u‖ * ‖v‖) (fun w => ?_)
    have hyv : _root_.GlobalTheory.RealWeil.Sm ρ (_root_.GlobalTheory.Mem.Lift.dH ρ v (y w)) := (hcal _ (hys w)).1 v
    rw [(hcal _ (hys w)).2.2.2.1 v w, _root_.GlobalTheory.Mem.Lift.dH_add u ((hcal _ hyv).2.1 w)
      (_root_.GlobalTheory.RealWeil.Osc.sm_smul _ (hFs w)), _root_.GlobalTheory.Mem.Lift.dH_smul u _ (hFs w)]
    have e1 := norm_dH_action_le hJ h hyv u w
    have e2 := norm_dH_action_le hJ h (hys w) u w
    have e3 : ‖_root_.GlobalTheory.Mem.Lift.dH ρ u (_root_.GlobalTheory.Mem.Lift.dH ρ v (y w))‖ ≤ C2 * ‖y w‖ := by
      have := hC2' (y w); rwa [hyP] at this
    have e4 := hC1' w v
    have e5 := hC1' w u
    have e6 : ‖(2 * (π:ℂ) * Complex.I * ((_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J v w : ℝ) : ℂ))‖ ≤ 2 * π * (‖v‖ * ‖w‖) := by
      have : ‖(2 * (π:ℂ) * Complex.I * ((_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J v w : ℝ) : ℂ))‖ = 2 * π * |_root_.GlobalTheory.Mem.Lift.OscDeriv.omL J v w| := by
        simp [abs_of_pos Real.pi_pos]
      rw [this]; gcongr; exact abs_omL_apply_le v w
    have hpi := Real.pi_pos
    have n1 := norm_nonneg (y w)
    have n2 := norm_nonneg u
    have n3 := norm_nonneg v
    have n4 := norm_nonneg w
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (C2 * ‖y w‖ + 2 * π * (‖u‖ * ‖w‖) * (C1' * ‖v‖ * ‖y w‖)) +
          (2 * π * (‖v‖ * ‖w‖)) * (C1' * ‖u‖ * ‖y w‖ + 2 * π * (‖u‖ * ‖w‖) * ‖y w‖) := by
        rw [norm_smul]
        gcongr
        · exact e1.trans (by gcongr)
        · exact e2.trans (by gcongr)
      _ = _ := by ring
  have hquadint : Integrable (fun w => _root_.GlobalTheory.Mem.Lift.quad ρ c p q (ρ w (y w))) := by
    unfold _root_.GlobalTheory.Mem.Lift.quad
    exact integrable_finset_sum _ fun i _ => (hD2 _ _).smul (c i)
  have hD : ∫ w, (ρ w (_root_.GlobalTheory.Mem.Lift.quad ρ c p q (y w) + lam • y w) +
      fderiv ℝ (fun u => ρ u (y w)) w (X w)) = _root_.GlobalTheory.Mem.Lift.quad ρ c p q f + lam • f := by
    have hLim : ∀ w, ρ w (_root_.GlobalTheory.Mem.Lift.quad ρ c p q (y w) + lam • y w) +
        fderiv ℝ (fun u => ρ u (y w)) w (X w) =
        _root_.GlobalTheory.Mem.Lift.quad ρ c p q (ρ w (y w)) + lam • ρ w (y w) := by
      intro w
      rw [_root_.GlobalTheory.Mem.Lift.fderiv_eq_quad_comm V B _ ρ hself hb X κ c p q hQ' _ (hys w) w,
        map_add, map_smul]
      abel
    simp_rw [hLim]
    rw [integral_add hquadint (hFi.smul lam : Integrable (fun w => lam • ρ w (y w))), integral_smul, hres',
      ← quad_integral_eq_integral_quad hJ h c p q hFi hFs (by rw [hres']; exact hf) hD1 hD2, hres']
  obtain ⟨M, hM⟩ : ∃ M : ℝ → B → B, M = fun t x => ∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ (a t u) x := ⟨_, rfl⟩
  have hMd : ∀ t x, M t x = ∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ (a t u) x := by intro t x; rw [hM]
  have hfun : (fun t : ℝ => ∫ w, ρ (a t w) (∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ (a t u)
      (_root_.GlobalTheory.RealWeil.proj h (ρ (-w) f)))) = fun t => ∫ w, ρ (a t w) (M t (y w)) := by
    rw [hM, hy]
  have hM0 : ∀ x, M 0 x = _root_.GlobalTheory.RealWeil.proj h x := by
    intro x; rw [hMd, _root_.GlobalTheory.RealWeil.proj_apply]; simp [ha0]
  have hMint : ∀ t, Integrable (fun w => ρ (a t w) (M t (y w))) := by
    intro t
    have hh := _root_.GlobalTheory.RealWeil.UnitaryOsc.isHeis_comp h (a t) (hsym t)
    have := _root_.GlobalTheory.RealWeil.Osc.intw_integrable
      (T := (_root_.GlobalTheory.RealWeil.proj hh).comp (_root_.GlobalTheory.RealWeil.proj h)) hh
      (fun x => by simp only [ContinuousLinearMap.comp_apply, hPP]) hrd
    refine this.congr (ae_of_all _ fun w => ?_)
    simp only [ContinuousLinearMap.comp_apply, _root_.GlobalTheory.RealWeil.proj_apply hh, hMd, hy]
  have hF0 : ∀ w, ρ (a 0 w) (M 0 (y w)) = ρ w (y w) := by
    intro w; rw [hM0, hyP, ha0, ContinuousLinearMap.one_apply]
  have hslope : ∀ t : ℝ, t⁻¹ • ((∫ w, ρ (a t w) (M t (y w))) - ∫ w, ρ (a 0 w) (M 0 (y w))) =
      ∫ w, t⁻¹ • (ρ (a t w) (M t (y w)) - ρ w (y w)) := by
    intro t; rw [← integral_sub (hMint t) (hMint 0), ← integral_smul]; simp_rw [hF0]
  have decomp : ∀ (t : ℝ) w, t⁻¹ • (ρ (a t w) (M t (y w)) - ρ w (y w)) =
      ρ (a t w) (t⁻¹ • (M t (y w) - y w)) + t⁻¹ • (ρ (a t w) (y w) - ρ w (y w)) := by
    intro t w
    rw [ContinuousLinearMap.map_smul_of_tower, map_sub, ← smul_add]
    congr 1; abel
  rw [hfun, ← hD, hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add]
  refine Filter.Tendsto.congr (fun t => (hslope t).symm) ?_
  obtain ⟨K, hK, hKb⟩ := hX.isBigO_sub.exists_pos
  have hKev := hKb.bound
  have h1ev : ∀ᶠ t in 𝓝 (0:ℝ), |t| ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0:ℝ) one_pos] with t ht
    simpa [Real.norm_eq_abs] using ht
  refine tendsto_integral_filter_of_dominated_convergence
    (fun w => (C0 + K * (C1' + π * (1 + K) * ‖w‖) * ‖w‖) * ‖y w‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun t => ((hMint t).sub hFi).aestronglyMeasurable.const_smul _
  · filter_upwards [nhdsWithin_le_nhds (hC0.and (hKev.and h1ev)), self_mem_nhdsWithin]
      with t ⟨hCt, hKt, h1t⟩ ht0
    refine ae_of_all _ fun w => ?_
    have ht : t ≠ 0 := ht0
    have hta : |t| ≠ 0 := abs_ne_zero.mpr ht
    have hat : ‖a t w - w‖ ≤ K * |t| * ‖w‖ := by
      have e : a t w - w = (a t - a 0) w := by rw [ha0]; simp
      rw [e]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have := mul_le_mul_of_nonneg_right hKt (norm_nonneg w)
      simpa [Real.norm_eq_abs] using this
    have hatw : ‖a t w‖ ≤ (1 + K) * ‖w‖ := by
      calc ‖a t w‖ = ‖w + (a t w - w)‖ := by congr 1; abel
        _ ≤ ‖w‖ + K * |t| * ‖w‖ := (norm_add_le _ _).trans (by gcongr)
        _ ≤ (1 + K) * ‖w‖ := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t hK.le) (norm_nonneg w)
          linarith
    have hmv := norm_heis_action_sub_le hJ h (hys w) hC1'0 (hC1' w) (R := (1 + K) * ‖w‖) (w := w)
      (w' := a t w) (by nlinarith [norm_nonneg w, hK]) hatw
    have hc : ‖M t (y w) - y w‖ ≤ C0 * |t| * ‖y w‖ := by
      have := hCt (y w); rw [hyP] at this; rw [hMd]; exact this
    rw [decomp]
    calc _ ≤ _ := norm_add_le _ _
      _ = |t|⁻¹ * ‖M t (y w) - y w‖ + |t|⁻¹ * ‖ρ (a t w) (y w) - ρ w (y w)‖ := by
        rw [h.2.2.1, norm_smul, norm_smul, norm_inv, Real.norm_eq_abs]
      _ ≤ |t|⁻¹ * (C0 * |t| * ‖y w‖) +
          |t|⁻¹ * ((C1' + π * ((1 + K) * ‖w‖)) * ‖y w‖ * (K * |t| * ‖w‖)) := by
        gcongr
        refine hmv.trans ?_
        gcongr
      _ = _ := by field_simp
  · have := ((hint' 0).const_mul C0).add (((hint' 1).const_mul (K * C1')).add
      ((hint' 2).const_mul (K * π * (1 + K))))
    refine this.congr (ae_of_all _ fun w => ?_)
    simp only [pow_zero, pow_one, Pi.add_apply]; ring
  · refine ae_of_all _ fun w => ?_
    have haw : HasDerivAt (fun t => a t w) (X w) 0 := by
      simpa using hX.clm_apply (hasDerivAt_const (0:ℝ) w)
    have hu : Filter.Tendsto (fun t => a t w) (𝓝[≠] 0) (𝓝 w) := by
      simpa [ha0] using haw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hv : Filter.Tendsto (fun t : ℝ => t⁻¹ • (M t (y w) - y w)) (𝓝[≠] 0)
        (𝓝 (_root_.GlobalTheory.Mem.Lift.quad ρ c p q (y w) + lam • y w)) := by
      have := hlam (y w)
      rw [hyP, hasDerivAt_iff_tendsto_slope_zero] at this
      refine this.congr (fun t => ?_)
      rw [zero_add, ← hMd, ← hMd, hM0, hyP]
    have hd : DifferentiableAt ℝ (fun u => ρ u (y w)) w :=
      ((show ContDiff ℝ ∞ (fun v => ρ v (y w)) from hys w).differentiable (by simp)) w
    have h2 : HasDerivAt (fun t => ρ (a t w) (y w)) (fderiv ℝ (fun u => ρ u (y w)) w (X w)) 0 :=
      hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 haw (by simp [ha0])
    rw [hasDerivAt_iff_tendsto_slope_zero] at h2
    have h2' : Filter.Tendsto (fun t : ℝ => t⁻¹ • (ρ (a t w) (y w) - ρ w (y w))) (𝓝[≠] 0)
        (𝓝 (fderiv ℝ (fun u => ρ u (y w)) w (X w))) := by
      simpa [ha0] using h2
    exact ((tendsto_heis_action_apply h hu hv).add h2').congr (fun t => (decomp t w).symm)

end GlobalTheory.Mem.Lift.OscDeriv
