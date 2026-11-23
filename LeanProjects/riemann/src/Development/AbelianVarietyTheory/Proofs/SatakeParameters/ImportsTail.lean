import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.StatementF

namespace GlobalTheory.MatrixEntryBound

theorem entry_bound {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L}
    (hϖ : (Valued.v : L → WithZero (Multiplicative ℤ)) ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (Valued.v : L → WithZero (Multiplicative ℤ)) (ϖ ^ m * x) ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by simp [hx]⟩
  · have hv : (Valued.v : L → WithZero (Multiplicative ℤ)) x ≠ 0 := by
      simpa using hx
    refine ⟨(WithZero.log (Valued.v x)).toNat, fun m hm => ?_⟩
    rw [map_mul, map_pow, hϖ, ← WithZero.exp_log hv, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    have : WithZero.log (Valued.v x) ≤ (m : ℤ) := by
      have := Int.self_le_toNat (WithZero.log (Valued.v x)); omega
    simp; omega

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}, (Valued.v : L → WithZero (Multiplicative ℤ)) ϖ = WithZero.exp (-1 : ℤ) → ∀ (M : Matrix (Fin n) (Fin n) L), ∃ (N : ℕ), ∀ (i j : Fin n), ϖ ^ N * M i j ∈ Formalism.UG.intL L := by
  intro L _ _ n ϖ hϖ M
  choose f hf using fun p : Fin n × Fin n => entry_bound hϖ (M p.1 p.2)
  refine ⟨Finset.univ.sup f, fun i j => ?_⟩
  unfold Formalism.UG.intL
  exact hf (i, j) _ (Finset.le_sup (f := f) (Finset.mem_univ (i, j)))

end GlobalTheory.MatrixEntryBound
