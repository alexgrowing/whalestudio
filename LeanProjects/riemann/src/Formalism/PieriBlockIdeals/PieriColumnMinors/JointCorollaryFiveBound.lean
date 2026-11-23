import Mathlib
import Formalism.PieriBlockIdeals.Statement
import Formalism.PieriBlockIdeals.StatementC
import Formalism.PieriBlockIdeals.JointCW5
import Formalism.PieriBlockIdeals.PieriColumnMinors.LabelSumNeedsLeFalse

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Formalism.RankGapBounds.ChebyshevFactorialBounds

lemma jw_Il_eq {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) :
    IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) = D.Icl τ l := by
  unfold IlInd Data.Icl
  by_cases h : ∃ y : ℤ, D.xlo τ ≤ y ∧ y ≤ D.xhi τ ∧ (l : ℤ) ∣ y - D.maxB τ
  · rw [if_pos h]
  · rw [if_neg h]

lemma jw_Icl_nonneg {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : 0 ≤ D.Icl τ l := by
  rw [← jw_Il_eq]
  unfold IlInd
  split_ifs <;> norm_num

lemma jw_gate_nonneg {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) :
    (0 : ℝ) ≤ (if ((D.d0 τ l : ℕ) : ℤ) < Cor.DB D τ then
        min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0) := by
  split_ifs
  · exact le_min (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact le_rfl

end Formalism.CohomologicalDescent
