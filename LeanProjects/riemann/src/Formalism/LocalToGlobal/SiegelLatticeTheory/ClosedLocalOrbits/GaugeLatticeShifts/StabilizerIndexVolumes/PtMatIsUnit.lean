import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

variable {K : Type*} [Field K]

def antiB (t : K) (s : ℕ) : Matrix (Fin s) (Fin s) K := fun i j => if i.val + j.val + 1 = s then t else 0

theorem antiB_sq (t : K) (s : ℕ) : antiB t s * antiB t s = (t * t) • (1 : Matrix (Fin s) (Fin s) K) := by
  ext i k
  have hi := i.isLt
  have hk := k.isLt
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Finset.sum_eq_single (⟨s - 1 - i.val, by omega⟩ : Fin s)]
  · simp only [antiB, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · intro j _ hj
    simp only [antiB]
    rw [if_neg, zero_mul]
    intro h
    apply hj
    ext
    show (j : ℕ) = s - 1 - i.val
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem antiB_det (t : K) (ht : t ≠ 0) (s : ℕ) : (antiB t s).det ≠ 0 := by
  intro h
  have h2 := congrArg Matrix.det (antiB_sq t s)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin] at h2
  exact pow_ne_zero s (mul_ne_zero ht ht) h2.symm

private theorem det_ptEntry_ne_zero_of_blocks : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ (n : ℕ), (bs.map Prod.snd).sum = n →
    (Matrix.of fun (a b : Fin n) => Formalism.MainNotions.S.ptEntry bs a.val b.val).det ≠ 0 := fun
  | [], _, n, hn => by
    simp only [List.map_nil, List.sum_nil] at hn
    subst hn
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  | (t, s) :: rest, hb, n, hn => by
    simp only [List.map_cons, List.sum_cons] at hn
    subst hn
    have ht : t ≠ 0 := (hb (t, s) (List.mem_cons_self ..)).1
    have hrest : ∀ b ∈ rest, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b hb' => hb b (List.mem_cons_of_mem _ hb')
    have ih := det_ptEntry_ne_zero_of_blocks rest hrest _ rfl
    have hM : (Matrix.of fun (a b : Fin (s + (rest.map Prod.snd).sum)) =>
        Formalism.MainNotions.S.ptEntry ((t, s) :: rest) a.val b.val).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (antiB t s) 0 0
          (Matrix.of fun (a b : Fin (rest.map Prod.snd).sum) => Formalism.MainNotions.S.ptEntry rest a.val b.val) := by
      ext (i | i) (j | j)
      all_goals
        have hi := i.isLt
        have hj := j.isLt
        simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.val_castAdd, Fin.val_natAdd, Matrix.of_apply, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.zero_apply, Formalism.MainNotions.S.ptEntry, antiB, Nat.add_sub_cancel_left]
        split_ifs <;> first | rfl | omega
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hM, Matrix.det_fromBlocks_zero₂₁]
    exact mul_ne_zero (antiB_det t ht s) ih

theorem ptMat_det {n : ℕ} (w : Formalism.MainNotions.S.Point K n) : (Formalism.MainNotions.S.ptMat w).det ≠ 0 := by
  have h := det_ptEntry_ne_zero_of_blocks w.1 w.2.1 n w.2.2
  exact h

theorem ptMat_isUnit {n : ℕ} (w : Formalism.MainNotions.S.Point K n) : IsUnit (Formalism.MainNotions.S.ptMat w).det :=
  isUnit_iff_ne_zero.mpr (ptMat_det w)

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
