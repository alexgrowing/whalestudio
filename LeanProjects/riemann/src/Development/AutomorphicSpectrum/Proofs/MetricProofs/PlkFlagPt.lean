import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesValueAtPoint
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_flagPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), M.IsFrame F → b ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal b) → (∀ τ', IsBlockDiag j (h τ')) → M.blk p = some k → FC.plk M F b (FC.flagPt M F b h) p = minorIJ (h p.1) (stepCols N j p.2) (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h p k hF hb hG hh hp
  have hCB := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (CovMap.LocImg.stepCols_ne_empty M.j_le)
  have hI₀ : IsStepRows N j p.2 (stepCols N j p.2) := CovMap.LocImg.FV.isStepRows_stepCols p.2
  have hdelta : ∀ J, IsStepRows N j p.2 J →
      ∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b =
        if stepCols N j p.2 = J then 1 else 0 := by
    intro J hJ
    have hu' := fun m : ι k => (hG.2.1 ⟨k, m⟩ (stepCols N j p.2)).2
    have hu := fun m : ι k => (hG.2.1 ⟨k, m⟩ J).1
    have e1 := (CovMap.LocImg.reg_sum hb Finset.univ (fun m : ι k => F.u' (stepCols N j p.2) ⟨k, m⟩ * F.u ⟨k, m⟩ J)
      fun m _ => (CovMap.LocImg.reg_mul hb (hu' m) (hu m)).1).2
    rw [hF.2.2.1 p k hp _ J hI₀ hJ] at e1
    rw [Finset.sum_congr rfl fun m _ => ((CovMap.LocImg.reg_mul hb (hu' m) (hu m)).2).symm, ← e1]
    split_ifs
    · exact map_one (CovMap.LocImg.regVal M.x hb)
    · exact map_zero (CovMap.LocImg.regVal M.x hb)
  have e1 : FC.plk M F b (FC.flagPt M F b h) p =
      ∑ J, (∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b) *
        minorIJ (h p.1) J (stepCols N j p.2) := by
    simp only [FC.plk, hp, Option.elim_some]
    simp_rw [flagPt_step M F b h hp, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e1, Finset.sum_eq_single (stepCols N j p.2)]
  · rw [hdelta _ hI₀, if_pos rfl, one_mul]
  · intro J _ hne
    by_cases hJ : IsStepRows N j p.2 J
    · rw [hdelta J hJ, if_neg hne.symm, zero_mul]
    · rw [hoff J hJ, mul_zero]
  · simp

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
