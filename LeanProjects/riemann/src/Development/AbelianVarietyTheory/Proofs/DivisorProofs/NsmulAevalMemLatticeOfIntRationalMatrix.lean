import Mathlib
open Matrix

namespace GlobalTheory

theorem nsmul_aeval_mem_lattice_of_intMatrix_basis (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (p : Polynomial ℚ) (D : ℕ) (hD : ∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) :
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by
  let φ : Module.End ℂ (Fin g → ℂ) →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun f => LinearMap.toMatrix e e (f.restrictScalars ℝ)
      map_one' := by
        rw [show ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 from rfl]
        exact LinearMap.toMatrix_one e
      map_mul' := fun f h => by
        rw [show ((f * h).restrictScalars ℝ) = (f.restrictScalars ℝ) * (h.restrictScalars ℝ) from rfl]
        exact LinearMap.toMatrix_mul e _ _
      map_zero' := by
        rw [show ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 from rfl]
        simp
      map_add' := fun f h => by
        rw [show ((f + h).restrictScalars ℝ) = (f.restrictScalars ℝ) + (h.restrictScalars ℝ) from rfl]
        simp
      commutes' := fun r => by
        have : ((algebraMap ℚ (Module.End ℂ (Fin g → ℂ)) r).restrictScalars ℝ) = algebraMap ℝ (Module.End ℝ (Fin g → ℂ)) (r : ℝ) := by
          refine LinearMap.ext fun x => funext fun i => ?_
          simp [Module.algebraMap_end_apply, Rat.smul_def]
        rw [this, LinearMap.toMatrix_algebraMap]
        ext i j
        simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
        }
  let ψ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ := (Algebra.ofId ℚ ℝ).mapMatrix
  have hψ : ∀ M : Matrix (Fin n) (Fin n) ℚ, ψ M = M.map (Rat.cast : ℚ → ℝ) := by
    intro M
    ext i j
    simp [ψ]
  have hφ : ∀ f : Module.End ℂ (Fin g → ℂ), φ f = LinearMap.toMatrix e e (f.restrictScalars ℝ) :=
    fun f => rfl
  have key : LinearMap.toMatrix e e ((Polynomial.aeval γ p).restrictScalars ℝ)
      = (Polynomial.aeval Tq p).map (Rat.cast : ℚ → ℝ) := by
    rw [← hφ, ← hψ, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hφ, hψ, hT]
  intro x hx
  choose m hm using (hΛ x).mp hx
  choose z hz using hD
  rw [hΛ]
  intro k
  refine ⟨∑ l, z k l * m l, ?_⟩
  have hv : ⇑(e.repr ((Polynomial.aeval γ p) x))
      = (Polynomial.aeval Tq p).map (Rat.cast : ℚ → ℝ) *ᵥ ⇑(e.repr x) := by
    rw [← key, LinearMap.toMatrix_mulVec_repr]
    rfl
  rw [LinearMap.smul_apply, map_nsmul, Finsupp.smul_apply, hv]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hm, nsmul_eq_mul, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  have := congrArg (Rat.cast : ℚ → ℝ) (hz k l)
  push_cast at this
  rw [← this]
  ring

theorem nsmul_aeval_mem_lattice_of_intMatrix : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ :=
  fun g n Λ e hΛ γ Tq hT p D hD => nsmul_aeval_mem_lattice_of_intMatrix_basis g n Λ e hΛ γ Tq hT p D hD

end GlobalTheory
