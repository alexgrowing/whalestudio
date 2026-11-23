import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem hasSignature_diag_signs (p q : ℕ) : Formalism.UG.HasSignature
    (Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ)) p q := by
  have hne : ∀ (i : Fin p) (j : Fin q), Fin.castAdd q i ≠ Fin.natAdd p j := fun i j h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  refine ⟨(finSumFinEquiv (m := p) (n := q)).symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply,
      Matrix.one_apply, (Fin.castAdd_injective p q).eq_iff]
    simp [Examples₂.sgn, Nat.not_le.2 i.isLt]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne i j)]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne j i).symm]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
      Matrix.neg_apply, Matrix.one_apply, (Fin.natAdd_injective q p).eq_iff]
    split_ifs <;> simp [Examples₂.sgn]

theorem exists_isV : ∀ (D : D7) (ν q : ℕ), q ≤ ν → ∃ X : LSp D, X.IsV ν q := by
  intro D ν q h
  obtain ⟨p, rfl⟩ : ∃ p, ν = p + q := ⟨ν - q, by omega⟩
  refine ⟨⟨diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q, GlobalTheory.PlaceModel.latFrame _⟩, rfl, fun τ => ?_,
    fun τ => ?_, GlobalTheory.PlaceModel.isSelfDualC_latFrame _⟩
  · have hg : (diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ =
        Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ) := by
      rw [diagSp_gram]
      ext i j
      change τ (if i = j then _ else 0) = if i = j then _ else 0
      by_cases hij : i = j <;> simp [hij, Examples₂.map_sgn]
    change Formalism.UG.HasSignature ((diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ) p q
    rw [hg]
    exact hasSignature_diag_signs p q
  · rw [Nat.add_sub_cancel]
    rfl

end GlobalTheory.ChiGrid
