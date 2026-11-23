import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.Development
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmRowForm

theorem sign_sq_cast {A : Type*} [Ring A] {t : ℕ} (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem double_row_decreasing : DblDec := by
  unfold DblDec
  intro A _ _ n t E hE a b u
  have hcol := Formalism.REAL.quantumMinorColSkew_holds A n t E hE a b
  unfold doubleRowFormSum
  rw [Finset.sum_comm]
  rw [show (t.factorial : ℂ) • qminor E a b u = ∑ _τ : Equiv.Perm (Fin t), qminor E a b u by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, Nat.cast_smul_eq_nsmul]]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := hcol τ u
  unfold qminor at h
  simp only [Function.comp_apply] at h
  have e : ∀ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : A) =
      ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign σ : ℤ) : A) := by
    intro σ
    rw [Int.cast_mul, (Int.cast_commute _ _).eq]
  simp_rw [e, mul_assoc, ← Finset.mul_sum]
  rw [h, ← mul_assoc, sign_sq_cast, one_mul]
  rfl

end PI.UnitaryGroupMassFormula.QmRowForm
