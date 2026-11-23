import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylRepInvMulDiag

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

theorem swap_lt_swap_iff_of_add_two {n : ℕ} (A A' a b : Fin n) (hA : A'.val = A.val + 2) (hab : a < b) :
    Equiv.swap A A' a < Equiv.swap A A' b ↔ (a < A ∨ A' < b) := by
  rw [Fin.lt_iff_val_lt_val] at hab
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h3 h4 <;>
    simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem val_rev_lo_of_last {n : ℕ} (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n) :
    ((lo k).rev : Fin n).val = (lo k).val + 2 := by
  have h2 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hn)
  have := k.isLt
  simp only [Fin.val_rev, lo, Fin.coe_castLE]
  omega

theorem mem_cellU_last_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ u : GU σ n, u ∈ cellU y ↔ IsUnipU u ∧ ∀ i j : Fin n, i < j → (i < lo k ∨ (lo k).rev < j) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro L _ _ _ ϖ σ q _ n k hk hn y _ hy u
  have hw : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hA := val_rev_lo_of_last k hk hn
  rw [hw] at hy
  rw [cellU, Subgroup.mem_subgroupOf, GKFactor.mem_cell_iff hy, mem_unipB, Equiv.swap_inv]
  unfold IsUnipU IsBorelU
  refine and_congr_right fun _ => forall₂_congr fun a b => ?_
  constructor
  · intro h hab hor
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).2 hor)
  · intro h hab hs
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).1 hs)

end WeylUnipotentShell

end WeylCell

end GlobalTheory
