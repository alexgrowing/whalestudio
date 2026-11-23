import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradicalStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem IsPrimitive.finsum_unipotentRadical_eq_zero (F : Type) [Field F] [Finite F] (d : ℕ)
    (φ : Module.End F (Fin d → F) → ℂ) (hφ : IsPrimitive φ) (a : ℕ) (ha : 0 < a) (had : a < d) :
    ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d,
      (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)},
      φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  obtain ⟨A, H, hA, hH, hbij⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F d a had.le
  have hbot : A ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hA
    omega
  have htop : A ≠ ⊤ := by
    rintro rfl
    rw [finrank_top, Module.finrank_fin_fun] at hA
    omega
  rw [← hH, ← hφ A hbot htop 1 (fun x hx => hx)]
  refine finsum_mem_eq_of_bijOn _ hbij fun u _ => ?_
  simp only [add_sub_cancel]

end GlobalTheory.CuspGL
