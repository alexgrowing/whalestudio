import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem blockRows_mem_Icc : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r, (Fm.D x i).R.k ≤ r → r < (Fm.D x i).R.N j → 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ≤ (Fm.L x i).etaSz := by
  intro eps Fm
  refine ⟨0, fun x _ _ i u j hj z r hk hr => ⟨(RowWeightLemmas.nuRow_pos _ u j hj _ r hr).le, ?_⟩⟩
  obtain ⟨q, s, hq, hs, rfl⟩ := RowWeightLemmas.block_decomp _ j r hk hr
  rw [RowWeightLemmas.nuRow_block _ u j hj _ q s hq hs, (Fm.D x i).hcW_e u]
  have h1 := (Fm.L x i).be_close (tauPl (Fm.D x i) z) ⟨q, by omega⟩ ⟨j, hj⟩
  have h2 := ((Fm.D x i).hc (tauPl (Fm.D x i) z)).gap_be ⟨q, by omega⟩
  have h3 : (0 : ℚ) ≤ ((j : ℚ) - q) * (((Fm.D x i).R.t : ℚ) + 1) := by
    have : (q : ℚ) ≤ j := by exact_mod_cast hq.le
    exact mul_nonneg (by linarith) (by positivity)
  have h4 : (0 : ℚ) ≤ (((Fm.D x i).R.t : ℚ) + 3) / 2 := by positivity
  refine le_trans ?_ h1
  refine le_trans ?_ (neg_le_abs _)
  rw [← Rat.cast_neg]
  exact Rat.cast_le.2 (by linarith)

end GlobalTheory
