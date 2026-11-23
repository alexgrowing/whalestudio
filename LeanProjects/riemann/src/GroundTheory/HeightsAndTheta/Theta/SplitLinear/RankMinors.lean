import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRowsLinearIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

namespace SplitLinear

open Matrix Module

universe u

variable {K : Type*} [Field K]

theorem exists_rows_linearIndependent {r : Type u} {c : Type*} [Fintype r] [Fintype c]
    (P : Matrix r c K) {k : ℕ}
    (hk : k ≤ P.rank) : ∃ I : Fin k → r, LinearIndependent K (fun p => P (I p)) :=
  _root_.UpperTheory.Reformulated.B.Qm10.exists_rows_linearIndependent P hk

theorem exists_minor_ne_zero {r c : Type*} [Fintype r] [Fintype c] (P : Matrix r c K) {k : ℕ}
    (hk : k ≤ P.rank) : ∃ (I : Fin k → r) (J : Fin k → c), (P.submatrix I J).det ≠ 0 := by
  classical
  obtain ⟨I, hI⟩ := exists_rows_linearIndependent P hk
  set N : Matrix (Fin k) c K := P.submatrix I id with hNdef
  have hN : N.rank = k := by
    have := LinearIndependent.rank_matrix (M := N) hI
    simpa using this
  have hNt : k ≤ Nᵀ.rank := by rw [rank_transpose, hN]
  obtain ⟨J, hJ⟩ := exists_rows_linearIndependent Nᵀ hNt
  refine ⟨I, J, ?_⟩
  have hQ : IsUnit (Nᵀ.submatrix J id) := linearIndependent_rows_iff_isUnit.1 hJ
  have e : P.submatrix I J = (Nᵀ.submatrix J id)ᵀ := by ext p q; rfl
  rw [e, det_transpose]
  exact ((isUnit_iff_isUnit_det _).1 hQ).ne_zero

end SplitLinear

end GroundTheory.Heights₂.Theta
