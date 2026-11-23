import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem flagPt_mem_mcPts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.flagPt M (BM.F l) (FC.bvec BM l b) h ∈ mcPts (mCoordIdeal y) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb h hh
  obtain ⟨hmem, hgood, hnorm, -⟩ := FC.bvec_good K ι Φ y Ψ N j M n BM l b hb
  have e := basePart_flagPt M (BM.F l) (FC.bvec BM l b) h
  refine CPts.flag_back M (BM.isFrame l) (by rw [e]; exact hmem) (by rw [e]; exact hgood) (h := h)
    ⟨fun k => by rw [e]; exact hnorm k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  rw [e, one_mul]
  exact flagPt_step M (BM.F l) (FC.bvec BM l b) h hp m

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
