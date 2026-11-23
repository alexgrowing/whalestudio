import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem isValueAt_coord_ratio :
    ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω]
      (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (k : K') (c : ι' k),
      z ∈ mcPts (mCoordIdeal y') → z ⟨k, c⟩ ≠ 0 →
        y' ⟨k, c⟩ ≠ 0 ∧ ∀ i : ι' k, IsValueAt y' (y' ⟨k, i⟩ / y' ⟨k, c⟩) z ((z ⟨k, c⟩)⁻¹ * z ⟨k, i⟩) := by
  intro K' _ ι' _ Ω _ y' z k c hz hzc
  have hy : y' ⟨k, c⟩ ≠ 0 := by
    intro h0
    have hm : (X ⟨k, c⟩ : MRing ι') ∈ mCoordIdeal y' := by
      refine RingHom.mem_ker.2 ?_
      simp [mConeMap, h0]
    have h1 := hz.2 _ hm
    simp only [map_X, eval_X] at h1
    exact hzc h1
  refine ⟨hy, fun i => ⟨fun l => if l = k then 1 else 0, X ⟨k, i⟩, X ⟨k, c⟩,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, c⟩, ?_, ?_, ?_, ?_⟩⟩
  · simpa using hy
  · simp only [aeval_X]
    field_simp
  · simpa using hzc
  · simp only [map_X, eval_X]
    rw [div_eq_inv_mul]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
