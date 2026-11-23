import Mathlib
import Formalism.FormalDegreeBessel.StatementRP

open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.LevelUnitary

def incl (k i r' : ℕ) : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * r' + k + 1)) ℂ :=
  fun p j => if p = levPos k i r' j then 1 else 0

def outer (k i r' : ℕ) : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ :=
  diagonal fun p => if i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then 0 else 1

variable (k i r' : ℕ)

theorem mul_incl {m : Type} (M : Matrix m (Fin (2 * (i + r') + k + 1)) ℂ) (p : m) (j) :
    (M * incl k i r') p j = M p (levPos k i r' j) := by
  simp [Matrix.mul_apply, incl]

theorem inclH_mul {m : Type} (M : Matrix (Fin (2 * (i + r') + k + 1)) m ℂ) (p : m) (j) :
    ((incl k i r')ᴴ * M) j p = M (levPos k i r' j) p := by
  simp [Matrix.mul_apply, incl, conjTranspose_apply, apply_ite star]

theorem incl_mul {m : Type} (M : Matrix (Fin (2 * r' + k + 1)) m ℂ) (p) (q : m) :
    (incl k i r' * M) p q =
      if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then M ⟨p.val - i, by omega⟩ q else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single ⟨p.val - i, by omega⟩]
    · have : p = levPos k i r' ⟨p.val - i, by omega⟩ := by
        apply Fin.ext; simp only [levPos]; omega
      rw [incl, if_pos this, one_mul]
    · intro b _ hb
      have : ¬ p = levPos k i r' b := by
        intro h; apply hb; apply Fin.ext
        have := congrArg Fin.val h
        simp only [levPos] at this ⊢; omega
      rw [incl, if_neg this, zero_mul]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    have : ¬ p = levPos k i r' b := by
      intro h; apply hp
      have := congrArg Fin.val h
      have hb := b.isLt
      simp only [levPos] at this ⊢; omega
    rw [incl, if_neg this, zero_mul]

theorem gram_inner : (incl k i r')ᴴ * Hpk k (i + r') * incl k i r' = Hpk k r' := by
  ext a b
  rw [mul_incl, inclH_mul]
  have ha := a.isLt
  have hb := b.isLt
  have hva : (levPos k i r' a).val = a.val + i := rfl
  have hvb : (levPos k i r' b).val = b.val + i := rfl
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.LevelUnitary
