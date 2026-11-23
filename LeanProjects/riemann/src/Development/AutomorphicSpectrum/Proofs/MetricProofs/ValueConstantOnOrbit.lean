import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem sameOrbit_symm' {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  rw [inv_mul_cancel_left₀ (hc p.1)]

theorem isValueAt_of_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ} {v : ℂ} (h : SameOrbit z z')
    (hv : IsValueAt x s z' v) : IsValueAt x s z v := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, g, f, hg, hf, hy, heq, hz0, rfl⟩ := hv
  have hprod : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, f, hg, hf, hy, heq, ?_, ?_⟩
  · rw [eval_smul_homog f d hf c]
    exact mul_ne_zero hprod hz0
  · rw [eval_smul_homog g d hg c, eval_smul_homog f d hf c, mul_div_mul_left _ _ hprod]

theorem valAt_eq_of_sameOrbit (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (z z' : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal x))
    (h : SameOrbit z z') : valAt x s z = valAt x s z' := by
  have hz' : z' ∈ mcPts (mCoordIdeal x) :=
    mem_mcPts_of_sameOrbit (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x)
      (sameOrbit_symm' h) hz
  by_cases hv : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := hv
    rw [valAt_eq hz hv, valAt_eq hz' (isValueAt_of_sameOrbit (sameOrbit_symm' h) hv)]
  · have hv' : ¬ ∃ v, IsValueAt x s z' v := fun ⟨v, hw⟩ => hv ⟨v, isValueAt_of_sameOrbit h hw⟩
    rw [valAt, valAt, dif_neg hv, dif_neg hv']

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
