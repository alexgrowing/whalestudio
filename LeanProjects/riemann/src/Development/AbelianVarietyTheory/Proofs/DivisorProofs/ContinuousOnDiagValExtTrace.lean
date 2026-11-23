import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff ENNReal ComplexOrder

namespace GlobalTheory

namespace HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem continuousOn_diagVal_extTrace {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {W : Set E}
    (hW : IsOpen W) (hK : ∀ v ∈ W, MContDiffAt ∞ K v) (hp : ∀ v ∈ W, (K v).PosDef) (ξ : E) :
    ContinuousOn (fun v => diagVal (extTrace K v) ξ) W := by
  intro v hv
  refine ContinuousAt.continuousWithinAt ?_
  have he : (fun w => diagVal (extTrace K w) ξ) =ᶠ[𝓝 v]
      fun w => (-Complex.I * (kappa * (secondForm K w ξ * secondFormAdj K w ξ).trace)).re := by
    filter_upwards [hW.mem_nhds hv] with w hw
    rw [diagVal, extTrace_eq ((hK w hw).of_le (by norm_cast))
      (eventually_of_mem (hW.mem_nhds hw) hp)]
  refine ContinuousAt.congr ?_ he.symm
  have hu : IsUnit (K v).det := (hp v hv).det_pos.ne'.isUnit
  have hsu : IsUnit (subGram (K v)).det := (posDef_subGram (hp v hv)).det_pos.ne'.isUnit
  have h0 : MContDiffAt 0 K v := (hK v hv).of_le (by simp)
  have hc : MContDiffAt 0 (fun w => conn K w ξ) v := (hK v hv).conn hu (by simp) ξ
  have hs : MContDiffAt 0 (fun w => secondForm K w ξ) v := fun a b => by
    simp only [secondForm_eq]; exact hc (Sum.inr a) (Sum.inl b)
  have ha : MContDiffAt 0 (fun w => secondFormAdj K w ξ) v :=
    ((h0.subGram.transpose.inv (by rwa [det_transpose])).mul hs.conjTranspose).mul
      (h0.quotGram hsu).transpose
  have hM := hs.mul ha
  have ht : ContinuousAt (fun w => (secondForm K w ξ * secondFormAdj K w ξ).trace) v := by
    simp only [Matrix.trace, Matrix.diag]
    exact (ContDiffAt.sum fun i _ => hM i i).continuousAt
  exact Complex.continuous_re.continuousAt.comp (f := fun w =>
    -Complex.I * (kappa * (secondForm K w ξ * secondFormAdj K w ξ).trace))
    (continuousAt_const.mul (continuousAt_const.mul ht))

end HermFrame

namespace Met

open HermFrame

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)}

theorem bcMeas_finiteAtFilter_nhds [SecondCountableTopology (CxPts p σ)] [T2Space (CxPts p σ)]
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (H : h.IsCInf)
    (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    (h.bcMeas hS h₁ h₃).FiniteAtFilter (𝓝 y) := by
  obtain ⟨a, ha⟩ := exists_adapted hS h₁ h₃ y
  set W := c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ a.U with hWdef
  have hWo : IsOpen W := ChartGlue.isOpen_over c.e (isOpen_ptsIn a.U)
  have hyW : c.e y ∈ W := ChartGlue.mem_over c.e hy ha
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWo _ hyW
  set B := Metric.closedBall (c.e y) (ε / 2) with hBdef
  have hBW : B ⊆ W := (Metric.closedBall_subset_ball (by linarith)).trans hεW
  have hBt : B ⊆ c.e.target := hBW.trans inter_subset_left
  set K : ReciprocityTheory.L2DbarEstimates.V 1 → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
    fun v => h.gram a.frame (c.e.symm v) with hKdef
  have hK : ∀ v ∈ W, MContDiffAt ∞ K v := fun v hv => by
    have hz := c.e.map_target hv.1
    have := (H.gram a.frame hv.2).mContDiffAt c hz
    rwa [c.e.right_inv hv.1] at this
  have hp : ∀ v ∈ W, (K v).PosDef := fun v hv => h.posDef_gram_frame hS a hv.2
  have hg := continuousOn_diagVal_extTrace hWo hK hp (EuclideanSpace.single 0 1)
  set T := c.e.symm '' B with hTdef
  have hTc : IsCompact T :=
    (isCompact_closedBall _ _).image_of_continuousOn (c.e.continuousOn_symm.mono hBt)
  have hTs : T ⊆ c.e.source := by
    rintro _ ⟨v, hv, rfl⟩; exact c.e.map_target (hBt hv)
  have hTB : c.e '' T = B := by
    rw [hTdef, Set.image_image]
    exact (Set.image_congr fun v hv => c.e.right_inv (hBt hv)).trans (Set.image_id' B)
  refine ⟨T, ?_, ?_⟩
  · refine mem_of_superset ((c.e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨hy, Metric.mem_ball_self (half_pos hε)⟩) fun z hz => ⟨c.e z, ?_, c.e.left_inv hz.1⟩
    exact Metric.ball_subset_closedBall hz.2
  · rw [bcMeas_apply hS h₁ h₃ c H hTc.isClosed.measurableSet hTs, hTB]
    have e : ∀ v ∈ B, ENNReal.ofReal (h.bcDens hS h₁ h₃ c (c.e.symm v)) =
        ENNReal.ofReal (2 * diagVal (extTrace K v) (EuclideanSpace.single 0 1)) := fun v hv => by
      rw [bcDens_eq hS h₁ h₃ a c H (c.e.map_target (hBt hv)) (hBW hv).2, bcForm,
        c.e.right_inv (hBt hv)]
    rw [setLIntegral_congr_fun Metric.isClosed_closedBall.measurableSet e]
    exact Integrable.lintegral_lt_top (((continuousOn_const.mul (hg.mono hBW))).integrableOn_compact
      (isCompact_closedBall _ _))

end Met

theorem VMetric.bcFinite_of_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k),
    IsProjOver p → GenSmooth p 1 → ∀ (S : ShortComplex X.Modules) (r s : ℕ)
    (h : VMetric p S.X₂ (r + s)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s),
    h.IsCInf → h.BcFinite hS h₁ h₃ := by
  intro k _ X p hp hg S r s h hS h₁ h₃ H σ
  have := CxPts.compactSpace σ hp
  have := CxPts.secondCountableTopology_of_isProjOver σ hp
  have := CxPts.t2Space_cxPts_of_isProjOver σ hp
  obtain ⟨R⟩ := hg σ
  refine (isCompact_univ.measure_lt_top_of_nhdsWithin fun y _ => ?_).ne
  obtain ⟨i, hi⟩ := R.cover y
  exact (Met.bcMeas_finiteAtFilter_nhds hS h₁ h₃ (H σ) (R.chart i) hi).filter_mono
    nhdsWithin_le_nhds

end GlobalTheory
