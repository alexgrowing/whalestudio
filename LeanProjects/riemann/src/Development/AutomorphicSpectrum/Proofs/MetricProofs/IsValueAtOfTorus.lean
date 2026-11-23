import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

noncomputable def scaleT (c : K → ℂ) : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
theorem scaleT_inv_scaleT (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (f : MvPolynomial K ℂ) :
    scaleT (fun k => (c k)⁻¹) (scaleT c f) = f := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact DFunLike.congr_fun h f

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mConeMap_torus (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    mConeMap (fun q : Σ k, ι k => c q.1 * z q) f = scaleT c (mConeMap z f) := by
  have h : mConeMap (fun q : Σ k, ι k => c q.1 * z q) =
      ((scaleT c).restrictScalars ℤ).comp (mConeMap z) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [mConeMap, scaleT, AlgHom.comp_apply, aeval_X, AlgHom.restrictScalars_apply, map_mul,
      algHom_C, algebraMap_eq, mul_assoc]
    rw [mul_left_comm]
  rw [h]
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mCoordIdeal_torus (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z := by
  ext f
  rw [mCoordIdeal, mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_torus]
  constructor
  · intro h
    have := congrArg (scaleT fun k => (c k)⁻¹) h
    rwa [scaleT_inv_scaleT c hc, map_zero] at this
  · intro h
    rw [h, map_zero]

theorem isValueAt_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s z v) :
    IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v := by
  obtain ⟨d, g, h, hg, hh, hy, he, h0, rfl⟩ := hv
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero hu h0
  · rw [eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

theorem isValueAt_of_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v) :
    IsValueAt x s z v := by
  have h := isValueAt_torus (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hv
  have e : (fun q : Σ k, ι k => (c q.1)⁻¹ * (c q.1 * z q)) = z := by
    funext q
    exact inv_mul_cancel_left₀ (hc q.1) _
  rwa [e] at h

theorem valAt_torus {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : z ∈ mcPts (mCoordIdeal x))
    (hcz : (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x)) (s : Ω) :
    valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z := by
  by_cases h : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := h
    rw [valAt_eq hz hv, valAt_eq hcz (isValueAt_torus c hc hv)]
  · have h' : ¬ ∃ v, IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v :=
      fun ⟨v, hv⟩ => h ⟨v, isValueAt_of_torus c hc hv⟩
    rw [valAt, valAt, dif_neg h, dif_neg h']

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z ∧
      (z ∈ mcPts (mCoordIdeal x) → (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x) ∧
        ∀ s : Ω, valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z) := by
  intro K _ ι _ Ω _ x z c hc
  refine ⟨mCoordIdeal_torus c hc z, fun hz => ?_⟩
  have hcz := mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal x) c hc hz
  exact ⟨hcz, valAt_torus c hc hz hcz⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct
