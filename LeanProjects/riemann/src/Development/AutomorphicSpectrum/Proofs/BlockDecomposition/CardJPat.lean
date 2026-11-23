import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatementStatement

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.WtFormPf

open ReciprocityTheory.Ty.Fin.Lq

section Dat

variable (g N : ℕ) [Fact g.Prime] [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
  (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ)

end Dat

theorem entN_eq {A : Type} [Semiring A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (x y : ℕ) :
    entN M x y = ∑ i : Fin N, ∑ j : Fin N, (if (i : ℕ) = x ∧ (j : ℕ) = y then (1 : A) else 0) * M i j := by
  unfold entN
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨x, h.1⟩ : Fin N), Finset.sum_eq_single (⟨y, h.2⟩ : Fin N)]
    · simp
    · intro j _ hj
      have : (j : ℕ) ≠ y := fun e => hj (Fin.ext e)
      simp [this]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ x := fun e => hi (Fin.ext e)
      simp [this]
    · simp
  · symm
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have : ¬ ((i : ℕ) = x ∧ (j : ℕ) = y) := by
      rintro ⟨rfl, rfl⟩
      exact h ⟨i.2, j.2⟩
    simp [this]

end GlobalTheory.CompanionTheory.TyFin.WtFormPf
