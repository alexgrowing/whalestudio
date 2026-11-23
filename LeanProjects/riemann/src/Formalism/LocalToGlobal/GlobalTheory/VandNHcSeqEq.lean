import Formalism.LocalToGlobal.GlobalTheory.CloudNonneg
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.HilbertSchmidtHalfBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightShiftProduct
import Formalism.LogVandermondeBounds.LogVandermondeProofs.LogRatioLowerBoundOfLogVandermondeGap
import Formalism.GL3MeanSquares.HookFormulaTorsion.IndicatorValueMemUnitInterval
import Formalism.LogVandermondeBounds.LogVandermondeProofs.UpperPlaceHolds
import Formalism.LogVandermondeBounds.LogVandermondeProofs.VandNSuccRight

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColOpen

open Formalism.BasicNotions Formalism.L2.Col Formalism.LogVandermondeBounds.StandardLattice Formalism.HermitianLattices.FormalDegreeBoundsAlt Formalism.HermitianLatticesTheory Finset

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem k_ge (R : Ranks) : 5 ≤ R.k := by
  have h1 := R.m_add_three_le_k
  have h2 := R.two_le_m
  omega

theorem one_lt_L (sc : Scale) : 1 < sc.L := Real.one_lt_rpow sc.one_lt_alt sc.eps_pos

section Shape

variable {W : Wts X Pr.Word R} {Δ S : ℝ} {c : X.Tau → ℝ} {code : Pr.Word → ℕ → ℕ}

theorem hcSeq_eq_colU (G : Grid W Δ S c code) (u : Pr.Word) (τ : X.Tau) {i : ℕ} (hi : i < R.k) :
    hcSeq W u τ i = colU R.k (c τ) Δ (code u) (hcSeq W u τ 0) (hcSeq W u τ (R.k - 1)) i := by
  unfold colU
  by_cases h0 : i = 0
  · rw [if_pos h0, h0]
  · rw [if_neg h0]
    by_cases h1 : i = R.k - 1
    · rw [if_pos h1, h1]
    · rw [if_neg h1]
      have hl : i - 1 < R.k - 2 := by omega
      have h2 := G.word u τ (i - 1) hl
      rw [show i - 1 + 1 = i by omega, G.cloud τ (i - 1) (by omega)] at h2
      rw [h2]
      rfl

theorem vandN_hcSeq_eq (G : Grid W Δ S c code) (u : Pr.Word) (τ : X.Tau) :
    vandN (hcSeq W u τ) R.k = vandN (colU R.k (c τ) Δ (code u) (hcSeq W u τ 0) (hcSeq W u τ (R.k - 1))) R.k :=
  Formalism.LogVandermondeBounds.StandardLattice.vandN_congr _ _ _ fun _ hi => hcSeq_eq_colU G u τ hi

theorem hcSeq_zero (W : Wts X Pr.Word R) (u : Pr.Word) (τ : X.Tau) :
    hcSeq W u τ 0 = (W.aTop u τ : ℝ) + ((R.k : ℝ) - 1) / 2 := by
  have h := aTop_eq_hc W u τ
  have hk := k_ge R
  unfold hcSeq
  rw [dif_pos (by omega)]
  exact h

theorem hcSeq_last (W : Wts X Pr.Word R) (u : Pr.Word) (τ : X.Tau) :
    hcSeq W u τ (R.k - 1) = -(W.bTop u τ : ℝ) - ((R.k : ℝ) - 1) / 2 := by
  have h := bTop_eq_hc W u τ
  have hk := k_ge R
  unfold hcSeq
  rw [dif_pos (by omega)]
  exact h

theorem hcSeq_zero_eq (hW : W.Ok) (u u' : Pr.Word) (τ : X.Tau) : hcSeq W u τ 0 = hcSeq W u' τ 0 := by
  have hk := k_ge R
  unfold hcSeq
  rw [dif_pos (by omega), dif_pos (by omega), hW.u_first u u' τ (by omega)]

theorem hcSeq_last_eq (hW : W.Ok) (u u' : Pr.Word) (τ : X.Tau) : hcSeq W u τ (R.k - 1) = hcSeq W u' τ (R.k - 1) := by
  have hk := k_ge R
  unfold hcSeq
  rw [dif_pos (by omega), dif_pos (by omega), hW.u_last u u' τ (by omega)]

end Shape

end Formalism.L2.GlobalTheoryTheory.ColOpen
