import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

def inhNumberingFun (p : youngCells (![2, 1] : Fin 2 → ℕ)) : Fin 3 :=
  if p.1 = (0, 0) then 0 else if p.1 = (0, 1) then 1 else 2

theorem inhNumberingFun_bijective : Function.Bijective inhNumberingFun := by
  unfold inhNumberingFun
  decide

theorem inh_card_two_one : (youngCells (![2, 1] : Fin 2 → ℕ)).card = 3 := by decide

def inhNumbering :
    youngCells (![2, 1] : Fin 2 → ℕ) ≃ Fin (youngCells (![2, 1] : Fin 2 → ℕ)).card :=
  (Equiv.ofBijective _ inhNumberingFun_bijective).trans (finCongr inh_card_two_one.symm)

theorem Comb.inh_standard_two_one : IsStandard inhNumbering := by
  intro p q h1 h2
  change ((inhNumberingFun p : ℕ)) ≤ (inhNumberingFun q : ℕ)
  revert p q
  unfold inhNumberingFun
  decide

theorem Comb.inh_updateZero :
    IsAlt (alternantPsum 2 [1]) ∧ Antitone (![1, 1] : Fin 2 → ℕ) ∧
      1 ≤ (![1, 1] : Fin 2 → ℕ) 0 + stair 2 0 ∧
      ¬ Antitone (Function.update (![1, 1] : Fin 2 → ℕ) 0 ((![1, 1] : Fin 2 → ℕ) 0 - 1)) := by
  refine ⟨isAlt_vandermonde_mul_prod _, ?_, by decide, ?_⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro h
    have := h (show (0 : Fin 2) ≤ 1 by decide)
    simp at this

theorem Comb.inh_sortShift :
    Antitone (![2, 1] : Fin 2 → ℕ) ∧ 1 ≤ (![2, 1] : Fin 2 → ℕ) 0 + stair 2 0 ∧
      Function.Injective (Function.update (fun j => (![2, 1] : Fin 2 → ℕ) j + stair 2 j) 0
        ((![2, 1] : Fin 2 → ℕ) 0 + stair 2 0 - 1)) := by
  refine ⟨?_, by decide, ?_⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [stair, Function.update]

theorem Comb.inh_sortShiftDistinct :
    Function.Injective (![3, 1] : Fin 2 → ℕ) ∧ 1 ≤ 1 ∧ (0 : Fin 2) ≠ 1 ∧
      1 ≤ (![3, 1] : Fin 2 → ℕ) 0 ∧ 1 ≤ (![3, 1] : Fin 2 → ℕ) 1 := by
  refine ⟨?_, le_rfl, by decide, by decide, by decide⟩
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all

theorem Comb.inh_vandermondePsumOne :
    ∑ i, (![2, 0] : Fin 2 → ℕ) i = ∑ i, stair 2 i + 1 := by
  simp [Fin.sum_univ_two, stair]

end

end GroundTheory.Heights₂.Heights.RestTerms
