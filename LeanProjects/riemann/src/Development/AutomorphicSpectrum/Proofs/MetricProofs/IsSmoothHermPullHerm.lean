import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumSqCompBlockMap
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

theorem pullDeg_zero {K K' : Type} (κ : K → K') : pullDeg κ (0 : K → ℤ) = 0 := by
  funext k
  by_cases h : ∃ a, κ a = k
  · simp [pullDeg, Function.extend_def, h]
  · simp [pullDeg, Function.extend_def, h]

theorem isSmoothHerm_pullHerm {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm (pullHerm hv B) := by
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k', ι' k') → ℂ => fun q => z (v q)) :=
    contDiff_pi.2 fun q => contDiff_apply ℝ ℂ (v q)
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B.h ∘ fun z : (Σ k', ι' k') → ℂ => fun q => z (v q))
    {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ContDiffOn.comp hB hlin.contDiffOn ?_
  intro z hz k
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : q.1 = k := hv.1 (by rw [← hv.2.2.1 q, hq])
  obtain ⟨k₀, m⟩ := q
  simp only at h2
  subst h2
  exact ⟨m, by simpa [hq] using hi'⟩

theorem exists_stepLine : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N)
    (B : HermLine (stepIdx M p)), B.a = 0 → ∃ A : HermLine ι, A.a = M.dy p ∧ M.OnStep p A ∧
      (IsSmoothHerm B → IsSmoothHerm A) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
        Real.log (A.h z) = Real.log ((fsHerm ι (M.dy p)).h z) + Real.log (B.h (z ∘ stepV M p)) := by
  intro K _ ι _ Φ _ y Ψ N j M p B hB
  have hdy : ∀ k, M.dy p k ≠ 0 → k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) := by
    intro k hk
    by_cases h : ∀ p', M.blk p' ≠ some k
    · exact ⟨⟨k, Or.inl h⟩, rfl⟩
    · by_cases h' : M.blk p = some k
      · exact ⟨⟨k, Or.inr h'⟩, rfl⟩
      · exact absurd (show M.dy p k = 0 by unfold FlagModel.dy; rw [dif_neg h, if_neg h']) hk
  refine ⟨(fsHerm ι (M.dy p)).tensor (pullHerm (isBlockMap_stepV M p) B), ?_, ?_, ?_, ?_⟩
  · show M.dy p + pullDeg _ B.a = M.dy p
    rw [hB, pullDeg_zero, add_zero]
  · intro z z' hb hs
    have hc : z ∘ stepV M p = z' ∘ stepV M p := by
      funext ⟨⟨k, hk⟩, m⟩
      rcases hk with h | h
      · exact congrFun hb ⟨⟨k, h⟩, m⟩
      · exact hs k h m
    show (fsHerm ι (M.dy p)).h z * B.h (z ∘ stepV M p) = (fsHerm ι (M.dy p)).h z' * B.h (z' ∘ stepV M p)
    rw [StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z
        (isBlockMap_stepV M p) hdy,
      StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z'
        (isBlockMap_stepV M p) hdy, hc]
  · intro hS
    exact isSmoothHerm_tensor (FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (isSmoothHerm_pullHerm (isBlockMap_stepV M p) hS)
  · intro z hz
    have h1 := (fsHerm ι (M.dy p)).pos z hz
    have h2 := (pullHerm (isBlockMap_stepV M p) B).pos z hz
    exact Real.log_mul h1.ne' h2.ne'

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine
