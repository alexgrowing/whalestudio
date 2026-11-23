import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeviProj

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.WhitHered

variable {N c : ℕ} (m : Fin c → ℕ) (hN : ∑ a, m a = N)

theorem sum_rev_eq (hN : ∑ a, m a = N) : ∑ b, m (Fin.revPerm b) = N := by
  rw [← hN]
  exact Equiv.sum_comp Fin.revPerm m

def revPlace : Fin N ≃ Fin N :=
  (stdBlocks (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN)).symm.trans
    ((Equiv.sigmaCongrLeft (β := fun a => Fin (m a)) Fin.revPerm).trans (stdBlocks m hN))

theorem revPlace_apply (b : Fin c) (j : Fin (m (Fin.revPerm b))) :
    revPlace m hN (stdBlocks (fun b => m (Fin.revPerm b)) (sum_rev_eq m hN) ⟨b, j⟩) = stdBlocks m hN ⟨Fin.revPerm b, j⟩ := by
  rw [revPlace, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply]
  rfl

variable (k : Type) [Field k]

def longW : GL (Fin N) k := (Matrix.permMatrixHom (R := k)).toHomUnits (revPlace m hN)

theorem longW_apply (i j : Fin N) :
    ((longW m hN k : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = if i = revPlace m hN j then 1 else 0 := by
  simp only [longW, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Equiv.Perm.inv_def, Option.mem_def, Option.some.injEq]
  by_cases h : i = revPlace m hN j
  · subst h; simp
  · rw [if_neg h, if_neg]; intro h'; exact h (by rw [← h']; simp)

theorem longW_conj_apply (A : GL (Fin N) k) (i j : Fin N) :
    (((longW m hN k)⁻¹ * A * longW m hN k : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      (A : Matrix (Fin N) (Fin N) k) (revPlace m hN i) (revPlace m hN j) := by
  have hinv : ∀ i j, (((longW m hN k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      if j = revPlace m hN i then 1 else 0 := by
    intro i j
    simp only [longW, ← map_inv, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, inv_inv,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, eq_comm]
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (revPlace m hN j)]
  · rw [longW_apply, if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (revPlace m hN i)]
    · rw [hinv, if_pos rfl, one_mul]
    · intro b _ hb
      rw [hinv, if_neg hb, zero_mul]
    · simp
  · intro b _ hb
    rw [longW_apply, if_neg hb, mul_zero]
  · simp

end GlobalTheory.WhitHered

end
