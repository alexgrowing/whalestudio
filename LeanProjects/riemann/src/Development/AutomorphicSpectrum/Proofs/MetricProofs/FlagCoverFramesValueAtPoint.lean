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

theorem stepCols_ne_empty {N j : ℕ} (hj : j ≤ N) {i : Fin N} : stepCols N j i ≠ ∅ := by
  intro e
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have h0 : N - j < N := by omega
    have : (⟨N - j, h0⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      omega
    rw [e] at this
    simp at this
  · have h0 : 0 < N := by have := i.2; omega
    have : (⟨0, h0⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      omega
    rw [e] at this
    simp at this

theorem img_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → (∀ τ, IsBlockDiag j (h τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', z ⟨k', m'⟩ = a * CovMap.LocImg.plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.img Cv F' F z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M'.blk z ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F' F (basePart M'.blk z) p.1 * h p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z F' F h hb hF' hF hG' hG hh hyp p k hp
  obtain ⟨k', hk'⟩ := exists_blk_cover M' hp
  obtain ⟨a, ha, hz⟩ := hyp p k' hk'
  have hCB := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (stepCols_ne_empty M.j_le)
  have hdelta : ∀ I' J, IsStepRows N j p.2 I' → IsStepRows N j p.2 J →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
        valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z) = if I' = J then 1 else 0 := by
    intro I' J hI hJ
    have hu' := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ I').2
    have hu := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ J).1
    have e1 := (reg_sum hb Finset.univ (fun m' : ι' k' => F'.u' I' ⟨k', m'⟩ * F'.u ⟨k', m'⟩ J)
      fun m' _ => (reg_mul hb (hu' m') (hu m')).1).2
    rw [hF'.2.2.1 p k' hk' I' J hI hJ] at e1
    rw [Finset.sum_congr rfl fun m' _ => ((reg_mul hb (hu' m') (hu m')).2).symm, ← e1]
    split_ifs
    · exact map_one (regVal M'.x hb)
    · exact map_zero (regVal M'.x hb)
  have hread : ∀ I', IsStepRows N j p.2 I' →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * minorIJ (h p.1) I' (stepCols N j p.2) := by
    intro I' hI
    have e1 : ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * ∑ J, (∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
          valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z)) * minorIJ (h p.1) J (stepCols N j p.2) := by
      simp_rw [hz, plk, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m' _ => ?_
      ring
    rw [e1]
    congr 1
    rw [Finset.sum_eq_single I']
    · rw [hdelta I' I' hI hI, if_pos rfl, one_mul]
    · intro J _ hne
      by_cases hJ : IsStepRows N j p.2 J
      · rw [hdelta I' J hI hJ, if_neg hne.symm, zero_mul]
      · rw [hoff J hJ, mul_zero]
    · simp
  refine ⟨a, ha, fun m => ?_⟩
  rw [img_step Cv F' F z hp hk' m]
  unfold stepCoord plk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hCB.1, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j p.2 I'
  · rw [if_pos hI, hread I' hI]; ring
  · rw [if_neg hI, hoff I' hI, mul_zero, mul_zero]

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
