import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NewPrimesSetDescription

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder

namespace GlobalTheory.Mean4

theorem gap_nonneg_of_dominant {D : D7} (Y : ShimX D.what₂.Tau) (u : Wt Y) (hu : Dominant Y u) (τ : D.what₂.Tau) :
    0 ≤ gap Y u τ := by
  unfold gap
  exact sub_nonneg.2 (hu τ _ _ (by simp [Fin.le_def]))

theorem nefCond_iInf {D : D7} (Y : ShimX D.what₂.Tau) (B q : ℝ) (hq : B ≤ q) (u : Wt Y) (hu : Dominant Y u)
    (h : NefCond Y B u) : 4 * (D.R.f : ℝ) * supAbs Y u ≤ (q - 2) * (⨅ τ, gap Y u τ) := by
  rcases isEmpty_or_nonempty D.what₂.Tau with he | hne
  · have h1 : supAbs Y u = 0 := by
      unfold supAbs
      exact Real.iSup_of_isEmpty _
    rw [h1, Real.iInf_of_isEmpty]
    simp
  · obtain ⟨τ, hτ⟩ := exists_eq_ciInf_of_finite (f := fun τ => gap Y u τ)
    rw [← hτ]
    exact (h τ).trans (mul_le_mul_of_nonneg_right (by linarith) (gap_nonneg_of_dominant Y u hu τ))

theorem positive_of_nef : ∀ (D : D7) (V : DivX D) (P : DIV.Align.PrinLev V) (S : HS D) (κ : V.Lev), HidaSetting D V S κ → DIV.Align.LevB P κ → NefHodgeTateLattices V P → Conclusion2 V P → ∀ A : SlopeTestRemainingChoices (V.shv S κ), (∀ (B : ℝ) (u : Wt (V.shv S κ)) (s : ℚ), 2 ≤ B → IsRat _ u → 0 < s → (∀ p ∈ setB (V.shv S κ) B, NefHT (V.shv S κ) p (A.sh u s)) → (∀ p : ℕ, p.Prime → p ∉ setB (V.shv S κ) B → NefDR (V.shv S κ) p (A.sh u s)) → (V.shv S κ).nefFib ((V.shv S κ).Mbar B u s)) → (∀ Λ : ℝ, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt (V.shv S κ)) (s : ℚ), IsRat _ u → supAbs _ u ≤ Λ → 0 < s → (s : ℝ) ≤ s₀ → Dominant _ (A.sh u s) → (V.shv S κ).semipos ((V.shv S κ).Mbar B u s)) → Positive A := by
  intro D V P S κ hS hL h1 h2 A hfib hsp Λ
  obtain ⟨s₀, hs₀, hsp⟩ := hsp Λ
  refine ⟨s₀, hs₀, fun B hB u s hu hΛ hs hss hd hc => ⟨hsp B hB u s hu hΛ hs hss hd, hfib B u s hB hu hs ?_ ?_⟩⟩
  · intro p hp
    exact h1 S κ hS hL p ((mem_setB_iff_le _ B p).1 hp).1 _ hd
  · intro p hp hn
    have h' : ¬ ((p : ℝ) ≤ B ∨ p ∣ 2 * dE D ∨ p ∈ (V.shv S κ).lev) := fun h => hn ((mem_setB_iff_le _ B p).2 ⟨hp, h⟩)
    simp only [not_or, not_le] at h'
    exact h2 S κ hS hL p hp h'.2.1 h'.2.2 _ hd (nefCond_iInf _ B p h'.1.le _ hd hc)

end GlobalTheory.Mean4
