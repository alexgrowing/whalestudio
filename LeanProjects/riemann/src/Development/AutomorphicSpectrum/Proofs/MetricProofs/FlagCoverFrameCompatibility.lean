import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem trans_blockDiag_det : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal b) → M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ τ, IsBlockDiag j (Cv.trans F' F b τ) ∧ (Cv.trans F' F b τ).det ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F' F hb hF' hF hG' hG τ
  have hT := hF.1 τ
  have hT' := hF'.1 τ
  have hdet : ((F.T τ).map Cv.φ).det ≠ 0 := by
    have e : ((F.T τ).map Cv.φ).det = Cv.φ (F.T τ).det := by
      rw [RingHom.map_det]; rfl
    rw [e]
    exact (map_ne_zero Cv.φ).2 hT.2
  have hu : IsUnit ((F.T τ).map Cv.φ).det := isUnit_iff_ne_zero.2 hdet
  have hu' : IsUnit (F'.T τ).det := isUnit_iff_ne_zero.2 hT'.2
  have hA : IsBlockDiag j (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) :=
    ((hT.1.map Cv.φ).inv hu).mul hT'.1
  have hreg := Cv.agree b hb F' F hF' hF hG' hG τ
  have hz : valMat M'.x b (1 : Matrix (Fin N) (Fin N) M'.Ω) = 1 := by
    have hring := ValRing.regAt_valAt_ring _ _ _ M'.x b hb
    ext a c
    by_cases e : a = c
    · subst e
      show valAt M'.x ((1 : Matrix (Fin N) (Fin N) M'.Ω) a a) b = _
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact hring.2.2.2.1
    · show valAt M'.x ((1 : Matrix (Fin N) (Fin N) M'.Ω) a c) b = _
      rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e]
      exact hring.2.2.1
  have hAB : (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) * ((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu', Matrix.nonsing_inv_mul _ hu]
  have hmul := (regMat_mul hb (fun a c => (hreg a c).1) (fun a c => (hreg a c).2)).2
  rw [hAB, hz] at hmul
  have htr : Cv.trans F' F b τ = valMat M'.x b (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) := rfl
  refine ⟨fun a c h => ?_, ?_⟩
  · show valAt M'.x ((((F.T τ).map Cv.φ)⁻¹ * F'.T τ) a c) b = 0
    rw [hA a c h]
    exact (ValRing.regAt_valAt_ring _ _ _ M'.x b hb).2.2.1
  · rw [htr]
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
