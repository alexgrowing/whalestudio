import Mathlib

open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.RowSect

theorem exists_GL_last_row (k : Type) [Field k] (m : ℕ) (ξ : Fin (m + 1) → k) (hξ : ξ ≠ 0) :
    ∃ h : GL (Fin (m + 1)) k,
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ᵥ* (h : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  classical
  have hs : LinearIndepOn k id ({ξ} : Set (Fin (m + 1) → k)) := (linearIndepOn_singleton_iff k).2 hξ
  have hmem : ξ ∈ hs.extend (Set.subset_univ _) := Module.Basis.subset_extend hs (Set.mem_singleton ξ)
  have hcard : Fintype.card (hs.extend (Set.subset_univ _)) = m + 1 := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.extend hs), Module.finrank_fin_fun]
  let e₀ := Fintype.equivFinOfCardEq hcard
  let e := e₀.trans (Equiv.swap (e₀ ⟨ξ, hmem⟩) (Fin.last m))
  have he : e.symm (Fin.last m) = ⟨ξ, hmem⟩ := by
    rw [Equiv.symm_apply_eq]
    simp [e]
  let b := (Module.Basis.extend hs).reindex e
  have hlast : b (Fin.last m) = ξ := by
    simp only [b, Module.Basis.reindex_apply, he, Module.Basis.extend_apply_self]
  have hu : IsUnit (Matrix.of fun i j => b i j) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 b.linearIndependent
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, single_vecMul, one_smul]
  exact hlast

end GlobalTheory.CompanionTheory.RowSect
