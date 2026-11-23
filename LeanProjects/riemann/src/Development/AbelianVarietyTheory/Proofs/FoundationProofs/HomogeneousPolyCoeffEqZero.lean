import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory

theorem homogeneous_poly_coeff_eq_zero (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (htf : ∀ (c : ℤ_[l]) (x : M), c ≠ 0 → c • x = 0 → x = 0) (w : ℕ) (c : Fin (w + 1) → M)
    (hv : ∀ u : Fin 2 → ℤ_[l], ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i = 0) :
    c = 0 := by
  set V : Matrix (Fin (w + 1)) (Fin (w + 1)) ℤ_[l] := Matrix.vandermonde (fun t : Fin (w + 1) => ((t : ℕ) : ℤ_[l])) with hVdef
  have hrow : ∀ t : Fin (w + 1), ∑ i, V t i • c i = 0 := by
    intro t
    have := hv ![((t : ℕ) : ℤ_[l]), 1]
    simpa [hVdef, Matrix.vandermonde_apply] using this
  have hdet : V.det ≠ 0 := by
    rw [hVdef, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    apply Fin.ext
    have hab' : ((a : ℕ) : ℤ_[l]) = ((b : ℕ) : ℤ_[l]) := hab
    exact_mod_cast hab'
  have key : ∀ j, V.det • c j = 0 := by
    intro j
    have h1 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = 0 := by simp [hrow]
    have h2 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = ∑ i, (V.adjugate * V) j i • c i := by
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
    rw [h2, Matrix.adjugate_mul] at h1
    simpa [Matrix.smul_apply, Matrix.one_apply, ite_smul, Finset.sum_ite_eq] using h1
  funext j
  exact htf _ _ hdet (key j)

end GlobalTheory
