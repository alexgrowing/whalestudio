import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelSourceSupportFiniteComponentInBoxStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem le_mul_ofReal_inv_of_mul_le {a b : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (h : a * ENNReal.ofReal ((1 + r) ^ N) ≤ b) : a ≤ b * ENNReal.ofReal (((1 + r) ^ N)⁻¹) := by
  have hpos : 0 < (1 + r) ^ N := by positivity
  rw [ENNReal.ofReal_inv_of_pos hpos, ← div_eq_mul_inv]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos)) (Or.inl ENNReal.ofReal_ne_top)]
  exact h

theorem mixS_le_maj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (U : AddSubgroup (WO S T)),
    IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ≥0,
    ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x w,
      ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤ C * supSob ψ θ N f * ENNReal.ofReal (maj θ K N x) := by
  intro D ψ hψ θ hθ S S₀ T ρ d v U hU
  obtain ⟨K, hK, hsupp⟩ := GlobalTheory.T.mixedModelSource_support_finiteComponentInBox D ψ hψ S S₀ T ρ d v U hU
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.mixedCoordinate_decay_realEntries D ψ hψ θ hθ S S₀ T ρ d v N
  refine ⟨C, fun f hf x w => ?_⟩
  by_cases h0 : d.mixS T ψ v.μ v.𝓕 f x w = 0
  · rw [h0]; simp
  · have hbox := hsupp f hf x w h0
    have hmaj : maj θ K N x = ((1 + realSize θ x) ^ N)⁻¹ := by
      unfold maj; rw [if_pos hbox]
    rw [hmaj]
    exact le_mul_ofReal_inv_of_mul_le (realSize_nonneg θ x) N (hC f hf.1 x w)

end GlobalTheory.Unf
