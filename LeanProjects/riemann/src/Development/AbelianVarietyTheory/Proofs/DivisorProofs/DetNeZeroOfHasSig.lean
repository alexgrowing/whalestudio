import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.SigDet

theorem det_ne_zero_of_hasSig : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → M.det ≠ 0 := by
  intro n M r s h
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  set B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm with hB
  have key : Bᵀ * M * B.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    have t1 : Bᵀ = Aᵀ.submatrix e.symm id := rfl
    have t2 : B.map star = (A.map star).submatrix id e.symm := rfl
    rw [t1, t2, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  rw [Matrix.det_neg] at hd
  simp at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

end GlobalTheory.SigDet
