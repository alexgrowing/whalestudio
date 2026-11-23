import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem ballPot_ballPt_eq : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ), ballPot q (ballPt q W) = -∑ τ, Real.log (1 - W τ * (W τ)ᴴ).det.re := by
  intro Ψ _ j j' n q W
  unfold ballPot
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hm : ballMat q (ballPt q W) τ = (W τ)ᵀ := by
    ext a b
    simp [ballMat, ballPt]
  have key : 1 - ((W τ)ᵀ)ᴴ * (W τ)ᵀ = (starRingEnd ℂ).mapMatrix (1 - W τ * (W τ)ᴴ) := by
    ext a b
    simp only [Matrix.sub_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, map_sub, map_sum, map_mul]
    congr 1
    · by_cases h : a = b <;> simp [Matrix.one_apply, h]
    · refine Finset.sum_congr rfl fun c _ => ?_
      simp
  rw [hm, key, ← RingHom.map_det, Complex.conj_re]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
